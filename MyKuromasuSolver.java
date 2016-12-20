import com.sun.org.apache.xerces.internal.impl.xpath.regex.Match;
import edu.kit.iti.formal.kuromasu.*;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Collectors;
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
				return dir.dx < 0 ? x : (width - 1) - y;
			}
		}

		@Override
		public String toString() {
			return "P(" + x + ", " + y + ")";
		}
	}

	class Number {
		int[] bits;

		Number(int numBits) {
			this.bits = new int[numBits];

			for(int i = 0; i < bits.length; ++i) {
				bits[i] = newVar();
			}
		}

		public int bits() {
			return bits.length;
		}

		public int bit(int i) {
			return bits[i];
		}

		public Number add(Number other) {
			Number result = new Number(Math.max(bits(), other.bits()) + 1);
			Number smaller = this;
			Number bigger = other;
			if(smaller.bits() > bigger.bits()) {

			}



			return result;
		}
	}

	private static final Direction NORTH = new Direction(0, -1);
	private static final Direction SOUTH = new Direction(0, 1);
	private static final Direction WEST = new Direction(-1, 0);
	private static final Direction EAST = new Direction(1, 0);

	private static final Direction[] DIRECTIONS = new Direction[] {
			NORTH, SOUTH, WEST, EAST
	};

	static final Direction[] SOUTH_EAST = new Direction[] {
			SOUTH, EAST
	};

	private int numFields;
	private int height;
	private int width;
	private int nextVar;

	public MyKuromasuSolver(Kuromasu k) {
		super(k);
		this.width = k.getWidth();
		this.height = k.getHeight();
		this.numFields = k.getHeight() * k.getWidth();
		this.nextVar = numFields + 1;
	}

	@Override
	public Solution solve() {
		// 1. Berechne die Klauselmenge für das in der Membervariable 'game'
		makeClausesForNeighbourCondition();
		makeClausesForVisibilityCondition();

		// 2. Rufe den SAT KuromasuSolver auf.
		try {
			if(solver.isSatisfiable()) {
				solution.setState(SolutionState.SAT);
				int[] model = this.solver.model();
				for(int idx = 1; idx <= numFields; ++idx)
				{
					boolean isBlack = solver.model(idx);
					Position pos = new Position(idx - 1);
					solution.setField(pos.y, pos.x, isBlack ?FieldValue.BLACK : FieldValue.WHITE);
				}

			}else {
				solution.setState(SolutionState.UNSAT);
			}
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
		// or on the terminal
		solution.print();

		return solution;
	}

	private void makeClausesForNeighbourCondition() {
		Iterable<Position> positions = positions()::iterator;
		for(Position pos : positions) {
			for(Position neighbour : pos.neighbours()) {
				addClause(-pos.isBlack(), -neighbour.isBlack());
			}
		}
	}

	private void makeClausesForVisibilityCondition() {
		for(NumberConstraint constraint : game.getNumberConstraints()) {
			Position pos = new Position(constraint.column, constraint.row);
			int visibleFields = constraint.value;

			int[][] variables = new int[DIRECTIONS.length][];

			// setup visibility into all directions
			for(int i = 0; i < DIRECTIONS.length; ++i) {
				Direction dir = DIRECTIONS[i];

				int numFields = pos.fieldsToBorder(dir);
				int[] vars = variables[i] = new int[numFields];


				Position cur = pos;
				for(int j = 0; j < numFields; ++j) {
					cur = cur.add(dir);

					int var = vars[j] = newVar();

					addClause(-var, cur.isBlack());

					Position no = pos;
					for(int k = 1; k < j; ++k) {
						no = no.add(dir);
						addClause(-var, -no.isBlack());
					}
				}
			}

			int[] first = makeClausesForAddition(variables[0], variables[1]);
			int[] second = makeClausesForAddition(variables[2], variables[3]);
			makeClausesForAddition(first, second, visibleFields, 0);
		}
	}

	private int[] makeClausesForAddition(int[] lhs, int[] rhs) {
		int max = lhs.length + rhs.length;
		int[] vars = new int[max + 1];
		for(int target = 0; target <= max; ++target) {
			int var = vars[target] = newVar();
			makeClausesForAddition(lhs, rhs, target, var);
		}
		return vars;
	}

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

	private int[][] allOf(int... args) {
		for(int arg : args) {
			addClause(arg);
		}
	}

	private void atLeastOneOf(int... args) {
		addClause(args);
	}

	private void noneOf(int... args) {
		for(int arg : args) {
			addClause(-arg);
		}
	}

	private void whenThen(int premise, int... conclusion) {
		for (int c : conclusion) {
			atLeastOneOf(-premise, c);
		}
	}

	private void exactlyOneOf(int... args) {
		int[] rest = new int[args.length - 1];

		for(int i = 0; i < args.length; ++i) {
			for(int j = 0; j < args.length; ++j) {
				if (i != j) {
					rest[j < i ? j : j - 1] = -args[j];
				}
			}
			whenThen(args[i], rest);
		}
		atLeastOneOf(args);
	}

	private void allOrNone(int... args) {
		for(int i = 0; i < args.length; ++i) {
			whenThen(args[i], rest(i, args));
		}
	}

	private int[] rest(int i, int... list) {
		int[] rest = new int[list.length - 1];
		for(int j = 0; j < list.length; ++j) {
			if (i != j) {
				rest[j < i ? j : j - 1] = list[j];
			}
		}
		return rest;
	}

	void test() {
		allOrNone(1, 2, 3, 4);
		atLeastOneOf(-2);

		try {
			if(solver.isSatisfiable()) {
				solution.setState(SolutionState.SAT);
				int[] model = this.solver.model();
				for (int i = 1; i <= 4; ++i) {
					System.out.println(i + " -> " + solver.model(i));
				}
			}else {
				System.out.println("Not satisfiable!");
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) {
		new MyKuromasuSolver(new Kuromasu()).test();
	}
}
