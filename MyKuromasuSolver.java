import edu.kit.iti.formal.kuromasu.*;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

import java.time.Duration;
import java.time.Instant;
import java.time.temporal.TemporalUnit;
import java.util.*;
import java.util.function.Function;
import java.util.function.IntUnaryOperator;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Bitte beschreie deine Implementierung.
 * @author  DEIN NAME UND MATRIKELNUMMER
 */
public class MyKuromasuSolver extends KuromasuSolver {

	static class Direction {
		final int dx;
		final int dy;

		Direction(int dx, int dy) {
			this.dx = dx;
			this.dy = dy;
		}

		@Override
		public String toString() {
			return "D(" + dx + ", " + dy + ")";
		}
	}

	class Position {
		final int x;
		final int y;

		Position(int x, int y) {
			this.x = x;
			this.y = y;
		}

		Position(int idx) {
			this.x = idx % width;
			this.y = idx / width;
		}

		Position add(Direction other) {
			return new Position(this.x + other.dx, this.y + other.dy);
		}
		Position add(Position other) {
			return new Position(this.x + other.x, this.y + other.y);
		}

		int toindex() {
			return x + y * width;
		}

		int isBlack() {
			return toindex() + 1;
		}

		int needsArrow() { return numFields + toindex() + 1; }

		private boolean isInField() {
			return 0 <= x && x < width
					&& 0 <= y && y < height;
		}

		private Position[] neighbours() {
			return neighbours(DIRECTIONS);
		}

		private Position[] neighbours(Direction[] dirs) {
			return Arrays.stream(dirs)
					.map(this::add)
					.filter(Position::isInField)
					.toArray(Position[]::new);
		}

		private int fieldsToBorder(Direction dir) {
			if(dir.dx == 0) {
				return dir.dy < 0 ? y : (height - 1) - y;
			} else {
				return dir.dx < 0 ? x : (width - 1) - x;
			}
		}

		@Override
		public String toString() {
			return "P(" + x + ", " + y + ")";
		}
	}

	class Number {
		private int max;
		protected int[] bits;

		Number(int max, int numBits) {
			if(max > 0) {
				if (max >= (int) Math.pow(2, numBits)) {
					throw new IllegalArgumentException("max to big");
				}
			} else {
				numBits = 0;
			}
			this.max = max;
			this.bits = new int[numBits];

			for(int i = 0; i < bits.length; ++i) {
				bits[i] = newVar();
			}
		}

		Number(int max) {
			this(max, (int)Math.floor(Math.log(max) / Math.log(2)) + 1);
		}

		int bits() {
			return bits.length;
		}

		int bit(int i) {
			return bits[i];
		}

		int max() {
			return max;
		}

		public Number add(Number other) {
			Number result = new Number(max() + other.max());
			Number smaller = bits() < other.bits()? this : other;
			Number bigger = bits() >= other.bits()? this : other;

			int carryIn = falseVar;
			for(int i = 0; i < smaller.bits(); ++i) {
				int big = bigger.bit(i);
				int small = smaller.bit(i);
				int res = result.bit(i);
				int carryOut = newVar();

				makeClausesForFullBitAdder(small, big, carryIn, carryOut, res);

				carryIn = carryOut;
			}

			for(int i = smaller.bits(); i < bigger.bits(); ++i) {
				int big = bigger.bit(i);
				int res = result.bit(i);
				int carryOut = newVar();

				// newCarry <=> big && carryIn
				addClause( carryOut, -carryIn, -big);
				addClause(-carryOut, carryIn);
				addClause(-carryOut, big);

				// res <=> big XOR carryIn
				addClause(-res, -carryIn, -big);
				addClause(-res, carryIn, big);
				addClause(res, -carryIn, big);
				addClause(res, carryIn,-big);

				carryIn = carryOut;
			}

			boolean extraBit = result.bits() > bigger.bits();
			addTerm(allOrNone(carryIn, extraBit? result.bit(result.bits() - 1) : falseVar));

			return result;
		}

		void equalTo(Number other, int... andCond) {
			Number smaller = bits() < other.bits()? this : other;
			Number bigger = bits() >= other.bits()? this : other;
			for(int i = 0; i < bigger.bits(); ++i) {
				int small = i < smaller.bits()? smaller.bit(i) : falseVar;
				int big = bigger.bit(i);

				// andCond => (small <=> big)
				int[] clause = new int[andCond.length + 2];
				int j;
				for(j = 0; j < andCond.length; ++j) {
					clause[j] = -andCond[j];
				}
				clause[j]     = small;
				clause[j + 1] = -big;
				addClause(clause);

				clause = clause.clone();
				clause[j]     = -small;
				clause[j + 1] = big;
				addClause(clause);
			}
		}

		private void makeClausesForFullBitAdder(int x, int y, int carryIn, int carryOut, int res) {
			// Clauses for fullbitadder's output
			// (carryIn && (x XOR y) || (x && y)) <=> carryOut
			addClause(-carryIn, carryOut, -x);
			addClause(-carryIn, carryOut, -y);
			addClause(carryIn, -carryOut, x);
			addClause(carryIn, -carryOut, y);
			addClause(-carryOut, x, y);
			addClause(carryOut, -x, -y);

			// carryIn XOR x XOR y <=> res
			addClause(-res, -x, -y, carryIn);
			addClause(-res, -x, y, -carryIn);
			addClause(-res, x, -y, -carryIn);
			addClause(-res, x, y, carryIn);
			addClause(res, -x, -y, -carryIn);
			addClause(res, -x, y, carryIn);
			addClause(res, x, -y, carryIn);
			addClause(res, x, y, -carryIn);
		}

		public String toString(ISolver solver) {
			StringBuilder bld = new StringBuilder();
			bld.append("[");
			int num = 0;
			int setter = 1 << bits() - 1;
			for(int i = bits() - 1; i >= 0; --i) {
				boolean isSet = solver.model(bit(i));
				bld.append(isSet? 1 : 0);
				num |= isSet? setter : 0;
				setter >>= 1;
			}

			bld.append("](");
			bld.append(num);
			bld.append(")");

			return bld.toString();
		}
	}

	class Constant extends Number {

		Constant(int c) {
			super(c);

			for(int i = 0; i < bits(); ++i) {
				int tester = 1 << i;
				bits[i] = ((c & tester) == 0)? falseVar : trueVar;
			}
		}
	}

	private static final Direction NORTH = new Direction(0, -1);
	private static final Direction SOUTH = new Direction(0, 1);
	private static final Direction WEST = new Direction(-1, 0);
	private static final Direction EAST = new Direction(1, 0);

	private static final Direction NORTH_WEST = new Direction(-1, -1);
	private static final Direction NORTH_EAST = new Direction( 1, -1);
	private static final Direction SOUTH_WEST = new Direction(-1,  1);
	private static final Direction SOUTH_EAST = new Direction( 1,  1);

	private static final Direction[] DIRECTIONS = new Direction[] {
			NORTH, SOUTH, WEST, EAST
	};

	private static final Direction[] DIAG_DIRS = new Direction[] {
			NORTH_WEST, SOUTH_WEST, SOUTH_EAST, NORTH_EAST
	};

	private int numFields;
	private int height;
	private int width;
	private int nextVar;
	private int falseVar;
	private int trueVar;

	public MyKuromasuSolver(Kuromasu k) {
		super(k);
		this.width = k.getWidth();
		this.height = k.getHeight();
		this.numFields = k.getHeight() * k.getWidth();
		this.nextVar = numFields * 2 + 1;

		// register static vars
		falseVar = newVar();
		addClause(-falseVar);

		trueVar = newVar();
		addClause(trueVar);
	}

	@Override
	public Solution solve() {
		Instant startCreation = Instant.now();
		// 1. Berechne die Klauselmenge für das in der Membervariable 'game'
		makeClausesForNeighbourCondition();
		makeClausesForVisibilityCondition();
		int[][][] arrows = makeClausesForReachabilityCondition();

		Instant afterClauses = Instant.now();

		// 2. Rufe den SAT KuromasuSolver auf.
		try {
			boolean solvable = solver.isSatisfiable();
			Instant afterSolving = Instant.now();


			if(solvable) {
				solution.setState(SolutionState.SAT);
				int[] model = this.solver.model();
				for(int idx = 1; idx <= numFields; ++idx)
				{
					boolean isBlack = solver.model(idx);
					Position pos = new Position(idx - 1);
					solution.setField(pos.y, pos.x, isBlack ?FieldValue.BLACK : FieldValue.WHITE);
				}

				/*for(int y = 0; y < height; ++y) {
					for(int x = 0; x < width; ++x) {
						for(int i = 0; i < DIAG_DIRS.length; ++i) {
							int var = arrows[x][y][i];
							System.out.print(var > 0 == solver.model(Math.abs(var))? "A" : "H");
							//System.out.print(solver.model(new Position(x, y).needsArrow())? "J" : "N");
						}
						System.out.print("|");
					}
					System.out.println();
				}

				//solution.show();*/
				solution.print();
			}else {
				solution.setState(SolutionState.UNSAT);
			}

			System.out.println("Creation: " + Duration.between(startCreation, afterClauses).toMillis());
			System.out.println("Solving:  " + Duration.between(afterClauses, afterSolving).toMillis());
		} catch (TimeoutException e) {
			e.printStackTrace();
		}

		// 3. Lese aus dem SAT KuromasuSolver heraus, welche Felder schwarz/weiß sind.

		//Angeben, ob eine Lösung vorliegt.


		//solution.setState(SolutionState.UNSAT);
		//solution.setState(SolutionState.SAT);

		// Have a lot of fun.

		// Visualize the Solution
		//solution.show();
		//, on the terminal

		return solution;
	}

	private void makeClausesForNeighbourCondition() {
		Iterable<Position> positions = positions()::iterator;
		for(Position pos : positions) {
			for(Position neighbour : pos.neighbours()) {
				if(pos.toindex() < neighbour.toindex()) {
					addClause(-pos.isBlack(), -neighbour.isBlack());
				}
			}
		}
	}

	private void makeClausesForVisibilityCondition() {
		for(NumberConstraint constraint : game.getNumberConstraints()) {
			Position pos = new Position(constraint.column, constraint.row);
			int visibleFields = constraint.value;

			// make number field always white
			addClause(-pos.isBlack());

			int[][] variables = new int[DIRECTIONS.length][];

			// setup visibility into all directions
			for(int i = 0; i < DIRECTIONS.length; ++i) {
				Direction dir = DIRECTIONS[i];

				int numFields = Math.min(visibleFields - 1, pos.fieldsToBorder(dir));
				int[] visibleCount = variables[i] = new int[numFields + 1];


				Position cur = pos;
				for(int j = 0; j < visibleCount.length; ++j) {
					cur = cur.add(dir);

					int var = visibleCount[j] = newVar();

					if(cur.isInField()) {
						// var => cur.isBlack()
						addClause(-var, cur.isBlack());
					}

					Position no = pos;
					for(int k = 0; k < j; ++k) {
						no = no.add(dir);
						// var => -no.isBlack()
						addClause(-var, -no.isBlack());
					}
				}
			}
			Number[] nums = Arrays.stream(variables).map(this::tieToNumber).toArray(Number[]::new);

			Number first = nums[0].add(nums[1]);
			Number second = nums[2].add(nums[3]);
			Number res = first.add(second);
			res.equalTo(new Constant(visibleFields - 1));
		}
	}

	private int[][][] makeClausesForReachabilityCondition() {
		int[][][] arrowPointsAway = new int[width][height][DIAG_DIRS.length];
		Number[][] selfReferencingIn = new Number[width][height];
		Number one = new Constant(1);
		for(int x = 0; x < width; ++x) {
			for(int y = 0; y < height; ++y) {
				selfReferencingIn[x][y] = new Number(width * height / 4);
			}
		}

		int outsideNeedsArrow = newVar();
		for(int x = 0; x < width; ++x) {
			for(int y = 0; y < height; ++y) {
				Position pos = new Position(x, y);

				// init arrowPointsAway
				int[] arrowAway = arrowPointsAway[x][y];
				for(int i = 0; i < DIAG_DIRS.length; ++i) {
					if(arrowAway[i] == 0) {
						Direction dir = DIAG_DIRS[i];
						Position to = pos.add(dir);
						if(to.isInField()) {
							int var = arrowAway[i] = newVar();
							// the value for 'to' points exactly in the opposite direction
							arrowPointsAway[to.x][to.y][(i + 2) % DIAG_DIRS.length] = -var;
						}else {
							// if at border, always point into border
							arrowAway[i] = trueVar;
						}
					}
				}

				// only black fields need an arrow
				// pos.needsArrow() => pos.isBlack()
				addClause(-pos.needsArrow(), pos.isBlack());

				for(int i = 0; i < DIAG_DIRS.length; ++i) {
					Position to = pos.add(DIAG_DIRS[i]);
					for(int j = i + 1; j < DIAG_DIRS.length; ++j) {
						Position snd = pos.add(DIAG_DIRS[j]);

						// 1) pos has >1 black neighbours => pos needs arrow
						if(to.isInField() && snd.isInField()) {
							// (pos.isBlack() & fst.isBlack() & snd.isBlack()) => pos.needsArrow()
							addClause(-pos.isBlack(), -to.isBlack(), -snd.isBlack(), pos.needsArrow());
						}else if(to.isInField() || snd.isInField()) {
							// exactly one is inField; the other is the border
							if(to.isInField()) {
								// (pos.isBlack() & fst.isBlack()) => pos.needsArrow()
								addClause(-pos.isBlack(), -to.isBlack(), pos.needsArrow());
							} else {
								// (pos.isBlack() & snd.isBlack()) => pos.needsArrow()
								addClause(-pos.isBlack(), -snd.isBlack(), pos.needsArrow());
							}
						}

						// 2) make sure max one arrow points away from a field that needs an arrow
						// pos.needsArrow() => -arrowAway[i] | -arrowAway[j]
						if(to.isInField() || snd.isInField()) {
							addClause(-pos.needsArrow(), -arrowAway[i], -arrowAway[j]);
						}
					}

					if(to.isInField()) {
						// 3) make sure arrows only point to a black field
						// pos.needsArrow() => (arrowAway[i] => fst.isBlack())
						addClause(-pos.needsArrow(), -arrowAway[i], to.isBlack());

						// add counting to the black fields to detect cycles
						Number pos_num = selfReferencingIn[pos.x][pos.y];
						Number to_num = selfReferencingIn[to.x][to.y];
						pos_num.add(one).equalTo(to_num, pos.needsArrow(), arrowAway[i]);
					}
				}

				// 2) make sure at least one arrow points away
				// pos.needsArrow() => one of arrowAway
				addTerm(when(pos.needsArrow()).then(atLeastOneOf(arrowAway)));
			}
		}
		return arrowPointsAway;
	}

	private Number tieToNumber(int[] fields) {
		if(fields.length <= 1) {
			return new Constant(0);
		}
		addClause(fields);
		Number result = new Number(fields.length - 1);
		for(int i = 0; i < fields.length; ++i) {
			int dist = i;
			result.equalTo(new Constant(dist), fields[i]);
		}
		return result;
	}

	/*private int[] makeClausesForAddition(int[] lhs, int[] rhs) {
		int max = lhs.length + rhs.length;
		int[] vars = new int[max + 1];
		for(int target = 0; target <= max; ++target) {
			int var = vars[target] = newVar();
			makeClausesForAddition(lhs, rhs, target, var);
		}
		return vars;
	}*/

	private void makeClausesForAddition(int[] lhs, int[] rhs, int targetValue, int targetVar) {
		for(int l = 0; l < lhs.length; ++l) {
			int r = targetValue - l;
			if(0 <= r && r < rhs.length) {
				if(targetVar != 0) {
					addClause(targetVar, -lhs[l], -rhs[r]);
				} else {
					addClause(-lhs[l], -rhs[r]);
				}
			}
		}
	}

	private Stream<Position> positions() {
		return IntStream
				.range(0, width)
				.mapToObj(x -> IntStream.range(0, height).mapToObj(y -> new Position(x, y)))
				.flatMap(p -> p);
	}

	private int newVar() {
		return nextVar++;
	}
	/**
	 * Adds the given literals as one clause to the sat solver instance.
	 * @param c the literals
	 */
	private void addClause(int... c) {
		try {
			// Debugging:
			// System.out.println(Arrays.toString(c));
			solver.addClause(new VecInt(c));
		} catch (ContradictionException e) {
			e.printStackTrace();
		}
	}

	private void addTerm(int[][] terms) {
		for(int[] term : terms) {
			addClause(term);
		}
	}

	private int[][] allOf(int... args) {
		return Arrays.stream(args)
				.mapToObj(o -> new int[]{o})
				.toArray(int[][]::new);
	}

	private int[][] allOf(int[][]... terms) {
		return Arrays.stream(terms)
				.flatMap(Arrays::stream)
				.toArray(int[][]::new);
	}

	private int[][] atLeastOneOf(int... args) {
		return new int[][]{args};
	}

	interface IndexBuilder {
		void build(int i);
	}

	private int[][] atLeastOneOf(int[][]... terms) {
		final int[][] dis = new int[terms.length][];
		final ArrayList<int[]> result = new ArrayList<>();

		final IndexBuilder builder = new IndexBuilder() {
			@Override
			public void build(int i) {
				if(i < terms.length) {
					int[][] src = terms[i];
					for (int[] v : src) {
						dis[i] = v;
						build(i + 1);
					}
				} else {
					result.add(Arrays.stream(dis)
							.flatMapToInt(Arrays::stream)
							.toArray());
				}
			}
		};

		builder.build(0);

		return result.toArray(new int[result.size()][]);
	}

	private int[][] noneOf(int... args) {
		return allOf(Arrays.stream(args).map(i -> -i).toArray());
	}

	private int[][] noneOf(int[][]... terms) {
		final ArrayList<int[]> result = new ArrayList<>();

		for(int[][] term : terms) {
			final int[] dis = new int[term.length];
			final IndexBuilder builder = new IndexBuilder() {
				@Override
				public void build(int i) {
					if (i < term.length) {
						int[] src = term[i];
						for (int v : src) {
							dis[i] = v;
							build(i + 1);
						}
					} else {
						result.add(Arrays.stream(dis).map(v -> -v).toArray());
					}
				}
			};
			builder.build(0);
		}

		return result.toArray(new int[result.size()][]);
	}

	interface When {
		int[][] then(int[][] conclusion);
		int[][] then(int... conclusion);
	}

	private When when(int[][] premise) {
		return new When() {
			@Override
			public int[][] then(int[][] conclusion) {
				return atLeastOneOf(noneOf(premise), conclusion);
			}

			@Override
			public int[][] then(int... conclusion) {
				return then(allOf(conclusion));
			}
		};
	}

	private When when(int... premise) {
		return when(allOf(premise));
	}

	private int[][] exactlyOneOf(int... args) {
		int[][][] conds = new int[args.length + 1][][];
		for(int i = 0; i < args.length; ++i) {
			int[] rest = rest(i, args);
			conds[i] = when(args[i]).then(noneOf(rest));
		}
		conds[conds.length - 1] = atLeastOneOf(args);
		return allOf(conds);
	}

	private int[][] exactlyOneOf(int[][]... args) {
		int[][][] conds = new int[args.length + 1][][];
		for(int i = 0; i < args.length; ++i) {
			int[][][] rest = rest(i, args);
			conds[i] = when(args[i]).then(noneOf(rest));
		}
		conds[conds.length - 1] = atLeastOneOf(args);
		return allOf(conds);
	}

	private int[][] allOrNone(int... args) {
		int[][][] conds = new int[args.length][][];
		for(int i = 0; i < args.length; ++i) {
			int[] rest = rest(i, args);
			conds[i] = when(args[i]).then(rest);
		}
		return allOf(conds);
	}

	private int[] rest(int i, int[] list) {
		int[] rest = new int[list.length - 1];
		for(int j = 0; j < list.length; ++j) {
			if (i != j) {
				rest[j < i ? j : j - 1] = list[j];
			}
		}
		return rest;
	}

	private int[][][] rest(int i, int[][][] list) {
		int[][][] rest = new int[list.length - 1][][];
		for(int j = 0; j < list.length; ++j) {
			if (i != j) {
				rest[j < i ? j : j - 1] = list[j];
			}
		}
		return rest;
	}

	private void test() throws ContradictionException {
		//int[][] term = noneOf(allOf(atLeastOneOf(1, 2), atLeastOneOf(3, 4)), allOf(atLeastOneOf(5, 6), atLeastOneOf(7, 8)));
		Number n = new Number(1);
		Number n2 = new Number(1);
		Number n3 = new Constant(2);
		//n2.add(n);
		n.add(n2).equalTo(n3, 100, 200);

		/*for(int[] t : term) {
			if(t.length > 0)
				solver.addClause(new VecInt(t));
		}*/

		try {
			ModelIterator mi = new ModelIterator(solver, 20);
			boolean unsat = true;
			while (mi.isSatisfiable()) {
				unsat = false;
				int[] model = mi.model();
				System.out.println("Instance (" + mi.numberOfModelsFoundSoFar() + "):");
				for (int m : model) {
					System.out.println(Math.abs(m) + " -> " + (m > 0));
				}

				System.out.println("n = " + n.toString(mi));
				System.out.println("n2 = " + n2.toString(mi));
				System.out.println("n3 = " + n3.toString(mi));
			}
			if(unsat) {
				System.out.println("Not satisfiable");
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) throws ContradictionException {
		new MyKuromasuSolver(new Kuromasu()).test();
	}
}
