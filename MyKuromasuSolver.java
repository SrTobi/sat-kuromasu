import edu.kit.iti.formal.kuromasu.*;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;

import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * Bitte beschreie deine Implementierung.
 * @author  DEIN NAME UND MATRIKELNUMMER
 */
public class MyKuromasuSolver extends KuromasuSolver {

	public enum FieldKnowledge {
		Unknown,
		White,
		Black
	}

	static class PuzzleContradictionException extends Exception {
		PuzzleContradictionException(String msg) {
			super(msg);
		}
	}

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

		int toIndex() {
			return x + y * width;
		}

		int isBlack() {
			return toIndex() + 1;
		}

		int isWhite() {
			return -isBlack();
		}

		int needsArrow() { return totalNumberOfFields + toIndex() + 1; }

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
		public boolean equals(Object other) {
			if(!(other instanceof Position)) {
				return false;
			}
			Position oth = (Position)other;
			return oth.x == x && oth.y == y;
		}

		@Override
		public int hashCode() {
			return toIndex();
		}

		@Override
		public String toString() {
			return "P(" + x + ", " + y + ")";
		}
	}

	class Number {
		private int max;
		int[] bits;

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

		Number add(Number other) {
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
			allOrNone(carryIn, extraBit? result.bit(result.bits() - 1) : falseVar);

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
	}

	// A constant number
	class Constant extends Number {
		Constant(int c) {
			super(c);

			for(int i = 0; i < bits(); ++i) {
				int tester = 1 << i;
				bits[i] = ((c & tester) == 0)? falseVar : trueVar;
			}
		}
	}

	// Axis aligned directions
	private static final Direction NORTH = new Direction(0, -1);
	private static final Direction SOUTH = new Direction(0, 1);
	private static final Direction WEST = new Direction(-1, 0);
	private static final Direction EAST = new Direction(1, 0);

	// Diagonal direcotions
	private static final Direction NORTH_WEST = new Direction(-1, -1);
	private static final Direction NORTH_EAST = new Direction( 1, -1);
	private static final Direction SOUTH_WEST = new Direction(-1,  1);
	private static final Direction SOUTH_EAST = new Direction( 1,  1);

	// List with all axis aligned directions
	private static final Direction[] DIRECTIONS = new Direction[] {
			NORTH, SOUTH, WEST, EAST
	};

	// List with all diagonal directions
	private static final Direction[] DIAG_DIRS = new Direction[] {
			NORTH_WEST, SOUTH_WEST, SOUTH_EAST, NORTH_EAST
	};

	// map to save already known fields
	private FieldKnowledge[][] knowledge;

	// total number of fields
	private int totalNumberOfFields;

	// height and width of the game's board
	private int height;
	private int width;

	private int nextVar;
	// the one var that is always false
	private int falseVar;

	// the one var that is always true
	private int trueVar;

	public MyKuromasuSolver(Kuromasu k) {
		super(k);
		this.width = k.getWidth();
		this.height = k.getHeight();
		this.totalNumberOfFields = k.getHeight() * k.getWidth();
		this.nextVar = totalNumberOfFields * 2 + 1;

		// register static vars
		falseVar = newVar();
		addClause(-falseVar);

		trueVar = newVar();
		addClause(trueVar);

		knowledge = new FieldKnowledge[width][height];
		Arrays.stream(knowledge).forEach(col -> Arrays.fill(col, FieldKnowledge.Unknown));
	}

	@Override
	public Solution solve() {
		try {
			Instant startCreation = Instant.now();
			// 1. Berechne die Klauselmenge für das in der Membervariable 'game'
			makeClausesForNeighbourCondition();
			if(!game.getNumberConstraints().isEmpty()) {
				makeClausesForVisibilityCondition();
				makeClausesForReachabilityCondition();
			}

			Instant afterClauses = Instant.now();

			try {
				// 2. Rufe den SAT KuromasuSolver auf.
				boolean solvable = solver.isSatisfiable();
				Instant afterSolving = Instant.now();


				if (solvable) {
					// 3. Lese aus dem SAT KuromasuSolver heraus, welche Felder schwarz/weiß sind.
					solution.setState(SolutionState.SAT);
					for (int idx = 1; idx <= totalNumberOfFields; ++idx) {
						boolean isBlack = solver.model(idx);
						Position pos = new Position(idx - 1);
						solution.setField(pos.y, pos.x, isBlack ? FieldValue.BLACK : FieldValue.WHITE);
					}

					solution.print();
				} else {
					solution.setState(SolutionState.UNSAT);
				}

				System.out.println("Creation: " + Duration.between(startCreation, afterClauses).toMillis());
				System.out.println("Solving:  " + Duration.between(afterClauses, afterSolving).toMillis());
			} catch (TimeoutException e) {
				e.printStackTrace();
			}
		} catch (PuzzleContradictionException e) {
			solution.setState(SolutionState.UNSAT);
		}

		return solution;
	}

	private void makeClausesForNeighbourCondition() {
		for(int x = 0; x < width; ++x) {
			for (int y = 0; y < height; ++y) {
				Position pos = new Position(x, y);
				for (Position neighbour : pos.neighbours()) {
					if (pos.toIndex() < neighbour.toIndex()) {
						addClause(pos.isWhite(), neighbour.isWhite());
					}
				}
			}
		}
	}

	private void makeClausesForVisibilityCondition() throws PuzzleContradictionException {
		int maxGlobalVisibleFields = width + height - 1;

		/*for(NumberConstraint constraint : game.getNumberConstraints()) {
			Position pos = new Position(constraint.column, constraint.row);

			// make number field always white
			//addClause(-pos.isBlack());
			knowledge[pos.x][pos.y] = FieldKnowledge.White;
		}*/

		for(NumberConstraint constraint : game.getNumberConstraints()) {
			Position pos = new Position(constraint.column, constraint.row);
			int targetVisibleFields = constraint.value;

			if(targetVisibleFields <= 0 || (targetVisibleFields == 1 && width > 1 && height > 1) || targetVisibleFields > maxGlobalVisibleFields) {
				throw new PuzzleContradictionException("Invalid number of visible fields");
			}

			addClause(pos.isWhite());
			knowledge[pos.x][pos.y] = FieldKnowledge.White;

			int[][] visibleCountSlotsTable = new int[DIRECTIONS.length][];
			int[] minVisibilityTable = new int[DIRECTIONS.length];

			// setup visibility into all directions
			for(int i = 0; i < DIRECTIONS.length; ++i) {
				Direction dir = DIRECTIONS[i];

				int maxVisibleFieldsIntoDir = Math.min(targetVisibleFields - 1, pos.fieldsToBorder(dir));
				int visibleFieldsIntoOtherDirs = maxGlobalVisibleFields - maxVisibleFieldsIntoDir;
				int minVis = minVisibilityTable[i] = Math.max(0, targetVisibleFields - visibleFieldsIntoOtherDirs);
				int[] visibleCountSlots = visibleCountSlotsTable[i] = new int[maxVisibleFieldsIntoDir + 1];


				Position cur = pos;
				for (int j = 0; j <= maxVisibleFieldsIntoDir; ++j) {
					if (0 < j && j <= minVis) {
						knowledge[cur.x][cur.y] = FieldKnowledge.White;
						addClause(cur.isWhite());
					}

					cur = cur.add(dir);

					if (j >= minVis) {

						int var = visibleCountSlots[j] = newVar();

						if (cur.isInField()) {
							// var => cur.isBlack()
							addClause(-var, cur.isBlack());
						}

						Position no = pos;
						for (int k = 0; k < j; ++k) {
							no = no.add(dir);
							// var => no.isWhite()
							if(k >= minVis) {
								addClause(-var, no.isWhite());
							}
						}
					}
				}
			}
			Number[] nums = IntStream
					.range(0, DIRECTIONS.length)
					.filter(i -> visibleCountSlotsTable[i].length > 1)
					.mapToObj(i -> tieToNumber(visibleCountSlotsTable[i], minVisibilityTable[i]))
					.toArray(Number[]::new);

			Number res = nums[0];

			if (nums.length == 2) {
				res = nums[0].add(nums[1]);
			} else if (nums.length == 3) {
				res = nums[0].add(nums[1]).add(nums[2]);
			} else if (nums.length == 4) {
				res = nums[0].add(nums[1]).add(nums[2].add(nums[3]));
			}

			res.equalTo(new Constant(targetVisibleFields - 1));
		}
	}

	// ties an array, where one true var defines the value of the number, to a binary number representation
	private Number tieToNumber(int[] visibleCountSlots, int minNum) {
		int maxNum = visibleCountSlots.length - 1;

		if(minNum == maxNum) {
			return new Constant(minNum);
		}
		atLeastOneOf(Arrays.copyOfRange(visibleCountSlots, minNum, visibleCountSlots.length));
		Number result = new Number(maxNum);
		for(int num = minNum; num <= maxNum; ++num) {
			result.equalTo(new Constant(num), visibleCountSlots[num]);
		}
		return result;
	}

	private void makeClausesForReachabilityCondition() {
		int[][][] arrowPointsAwayMap = new int[width][height][DIAG_DIRS.length];
		Number[][] selfReferencingInMap = new Number[width][height];
		Number one = new Constant(1);
		for(int x = 0; x < width; ++x) {
			for(int y = 0; y < height; ++y) {
				selfReferencingInMap[x][y] = new Number(width * height / 4);
			}
		}

		for(int x = 0; x < width; ++x) {
			for(int y = 0; y < height; ++y) {
				Position pos = new Position(x, y);

				// init arrowPointsAway
				int[] arrowAway = arrowPointsAwayMap[x][y];
				for(int i = 0; i < DIAG_DIRS.length; ++i) {
					if(arrowAway[i] == 0) {
						Direction dir = DIAG_DIRS[i];
						Position to = pos.add(dir);
						if(to.isInField()) {
							int var = arrowAway[i] = newVar();
							// the value for 'to' points exactly in the opposite direction
							arrowPointsAwayMap[to.x][to.y][(i + 2) % DIAG_DIRS.length] = -var;
						}else {
							// if at border, always point into border
							arrowAway[i] = trueVar;
						}
					}
				}

				// no need to construct the arrow stuff, if the field is white anyway
				if (knowledge[pos.x][pos.y] == FieldKnowledge.White) {
					addClause(-pos.needsArrow());
					continue;
				}

				// only black fields need an arrow
				// pos.needsArrow() => pos.isBlack()
				when(pos.needsArrow()).then(pos.isBlack());

				for(int i = 0; i < DIAG_DIRS.length; ++i) {
					Position to = pos.add(DIAG_DIRS[i]);
					for(int j = i + 1; j < DIAG_DIRS.length; ++j) {
						Position snd = pos.add(DIAG_DIRS[j]);

						// 1) pos has >1 black neighbours => pos needs arrow
						if(to.isInField() && snd.isInField()) {
							// (pos.isBlack() & fst.isBlack() & snd.isBlack()) => pos.needsArrow()
							whenAllOf(pos.isBlack(), to.isBlack(), snd.isBlack()).then(pos.needsArrow());
						}else if(to.isInField() || snd.isInField()) {
							// exactly one is inField; the other is the border
							if(to.isInField()) {
								// (pos.isBlack() & fst.isBlack()) => pos.needsArrow()
								whenAllOf(pos.isBlack(), to.isBlack()).then(pos.needsArrow());
							} else {
								// (pos.isBlack() & snd.isBlack()) => pos.needsArrow()
								whenAllOf(pos.isBlack(), snd.isBlack()).then(pos.needsArrow());
							}
						}

						// 2) make sure max one arrow points away from a field that needs an arrow
						// pos.needsArrow() => -arrowAway[i] | -arrowAway[j]
						if(to.isInField() || snd.isInField()) {
							when(pos.needsArrow()).thenOneOf(-arrowAway[i], -arrowAway[j]);
						}
					}

					if(to.isInField()) {
						// 3) make sure arrows only point to a black field
						// pos.needsArrow() => (arrowAway[i] => fst.isBlack())
						when(pos.needsArrow()).thenOneOf(-arrowAway[i], to.isBlack());

						// add counting to the black fields to detect cycles
						Number pos_num = selfReferencingInMap[pos.x][pos.y];
						Number to_num = selfReferencingInMap[to.x][to.y];
						pos_num.add(one).equalTo(to_num, pos.needsArrow(), arrowAway[i]);
					}
				}

				// 2) make sure at least one arrow points away
				// pos.needsArrow() => one of arrowAway
				whenAllOf(pos.needsArrow()).thenOneOf(arrowAway);
			}
		}
	}

	// Reserves a new variable from the variables-pool
	private int newVar() {
		return nextVar++;
	}

	/**
	 * Adds the given literals as one clause to the sat solver instance.
	 * @param c the literals
	 */
	private void addClause(int... c) {
		try {
			solver.addClause(new VecInt(c));
		} catch (ContradictionException e) {
			e.printStackTrace();
		}
	}

	// Makes clauses so that at least one var in args is true
	private void atLeastOneOf(int... args) {
		addClause(args);
	}

	// Interface for creating implications
	private interface When {
		void then(int conclusion);
		void thenOneOf(int... conclusion);
	}

	// Starts an implication
	private When whenAllOf(int... premise) {
		return new When() {
			@Override
			public void then(int conclusion) {
				thenOneOf(conclusion);
			}

			@Override
			public void thenOneOf(int... conclusion) {
				int[] clause = concat(premise, conclusion);
				for(int i = 0; i < premise.length; ++i) {
					clause[i] = -clause[i];
				}
				addClause(clause);
			}
		};
	}

	// Starts an implication
	private When when(int premise) {
		return whenAllOf(premise);
	}

	// Makes clauses, so that all vars in args at the same time are either true or false.
	private void allOrNone(int... args) {
		for(int i = 0; i < args.length; ++i) {
			for(int j = i + 1; j < args.length; ++j) {
				addClause( args[i], -args[j]);
				addClause(-args[i],  args[j]);
			}
		}
	}

	// Concatenates two arrays
	private static int[] concat(int[] first, int[] second) {
		int[] result = Arrays.copyOf(first, first.length + second.length);
		System.arraycopy(second, 0, result, first.length, second.length);
		return result;
	}
}
