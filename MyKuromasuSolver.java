import edu.kit.iti.formal.kuromasu.*;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * Mein Kuromasu Solver.
 *
 * @author Tobias Kahlert 1630395
 *
 * Die drei Funktionen makeClausesForNeighbourCondition, makeClausesForVisibilityCondition, makeClausesForReachabilityCondition
 * erzeugen die sat-Klauseln für die drei Regeln von Kuromasu.
 *
 * Zum zählen werden binär kodierte Zahlen verwendet, die per voll-bit-addierer zusammen addiert werden können.
 * Für die Sichtbarkeit gibt es ein paar Tricks schon vorher zu beweisen, dass manche Felder weiß sein müssen.
 *
 * Die wirkliche Besonderheit an der Lösung ist, dass der Zusammenhang der weißen Felder nicht über k-Erreichbarkeit modiliert ist,
 * sondern über das Fehlen von Kreisen bei schwarzen Feldern und Verbindungen von Spielfeldrand zu Spielfeldrand
 * über schwarze Felder. Dazu wird jedem schwarzen Feld, dass mindestens 2 schwarze Nachbarn hat (Rand ist dabei schwarz), ein Pfeil zugewiesen, der wiederum auf eines des
 * angrenzendes schwarzes Feld (mit möglicherweise nur einem schwarzen Nachbarn -> kein Pfeil) zeigen muss.
 * Zwei Felder dürfen nicht gegenseitig aufeinander zeigen und bei zwei schwarzen Feldern, die beide einen Pfeil brauchen,
 * muss einer von Beiden auf den anderen Zeigen. Pfeile am Rand müssen in den Rand hineinzeigen.
 * Gibt es dann zum Beispiel eine Verbindung von schwarzen Feldern vom Norden zum Süden, kann keine Richtung von Pfeilen zugewiesen werden,
 * da immer eine der beiden letzten Regeln verletzt wäre.
 *
 *      + - - - - +
 *      |   b     |
 *      |     b   |     <- Geht nicht, da rechte Seite von linker Seite getrennt... bzw schwarze Verbindung von Oben nach Unten.
 *      |   b     |
 *      + - - - - +
 *
 * Für Zyklen müssen weiterhin Zahlen vergeben werden, um k-selbstreferenzierung zu verhindern.
 *
 *      + - - - - - +
 *      |           |
 *      |     b     |   <- Geht nicht, da keine Verbindung von innen nach außen.
 *      |   b   b   |       Aber Pfeile vergeben möglich (rechts- oder linksherum).
 *      |     b     |       Aber ist 4-selbstreferenziert! => Erreichbarkeitsregel verletzt
 *      |           |
 *      + - - - - - +
 *
 */
public class MyKuromasuSolver extends KuromasuSolver {

	public enum FieldKnowledge {
		Unknown,
		White,
		Black
	}

	// Thrown when it can be proven that the puzzle is not solvable, because of obvious reasons
	static class PuzzleContradictionException extends RuntimeException {
		PuzzleContradictionException(String msg) {
			super(msg);
		}
	}

	// A direction on the board
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

	// A position on the board with a x and a y coordinate
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

		// Adds a direction on the position
		Position add(Direction other) {
			return new Position(this.x + other.dx, this.y + other.dy);
		}

		// Returns a unique index of the position
		//   Only valid for positions, that are on the board
		int toIndex() {
			assert isInField();
			return x + y * width;
		}

		// Returns the unique black sat-variable for this position.
		//   The returned variable, when true, indicates that the position has color black.
		//   Only valid for positions, that are on the board.
		int isBlack() {
			return toIndex() + 1;
		}

		// Returns the unique white sat-variable for this position.
		//   The returned variable, when true, indicates that the position has color white.
		//   Only valid for positions, that are on the board.
		int isWhite() {
			return -isBlack();
		}

		// Returns the unique sat-variable for this position, that indicates, that the position needs an arrow
		int needsArrow() { return totalNumberOfFields + toIndex() + 1; }

		// Returns if the position is on the puzzel board
		private boolean isInField() {
			return 0 <= x && x < width
					&& 0 <= y && y < height;
		}

		// Returns the axis aligned neighbours of the position
		private Position[] neighbours() {
			return neighbours(DIRECTIONS);
		}

		// Returns the neighbours position in the given dirs
		private Position[] neighbours(Direction[] dirs) {
			return Arrays.stream(dirs)
					.map(this::add)
					.filter(Position::isInField)
					.toArray(Position[]::new);
		}

		// Returns the number of fields to the border the given direction
		private int fieldsToBorder(Direction dir) {
			assert dir.dx == 0 || dir.dy == 0;
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

	// A number, represented by binary encoded sat-variables
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

		// Number of bits that compose this number
		int bits() {
			return bits.length;
		}

		// The variable of the i'th bit
		int bit(int i) {
			return bits[i];
		}

		// Returns the maximal number, that can be represented by this
		int max() {
			return max;
		}

		// Returns a number that is equal to the sum of this and other
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

		// ensures that other is equal to this, when all variables of andCond are true
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

		// creates the logic wirering for a full bit adder
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
			// 1. Berechne die Klauselmenge für das in der Membervariable 'game'
			makeClausesForNeighbourCondition();
			if(!game.getNumberConstraints().isEmpty()) {
				makeClausesForVisibilityCondition();
				makeClausesForReachabilityCondition();
			}

			try {
				// 2. Rufe den SAT KuromasuSolver auf.
				boolean solvable = solver.isSatisfiable();

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

			} catch (TimeoutException e) {
				e.printStackTrace();
			}
		} catch (PuzzleContradictionException e) {
			solution.setState(SolutionState.UNSAT);
		}

		return solution;
	}

	/**
	 * Ensures that two neighbouring fields are not both black.
	 */
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

	/**
	 * Ensures that a number field can see exactly as many fields as it's number demands.
	 * That is achieved by going into all directions from a number field and ensure that
	 * the sum of all visible fields match the wanted number.
	 */
	private void makeClausesForVisibilityCondition() {
		// the number of fields visible from a number field is bounded by the board size
		int maxGlobalVisibleFields = width + height - 1;

		// fields with only one width or height do not work well with the cycle thing
		// -> force inner fields to be white
		if(width == 1) {
			for (int y = 1; y < height - 1; ++y) {
				know(new Position(0, y), FieldKnowledge.White);
			}
		}

		if(height == 1) {
			for (int x = 1; x < width - 1; ++x) {
				know(new Position(x, 0), FieldKnowledge.White);
			}
		}

		for(NumberConstraint constraint : game.getNumberConstraints()) {
			Position pos = new Position(constraint.column, constraint.row);
			int targetVisibleFields = constraint.value;

			if(targetVisibleFields <= 0) {
				throw new PuzzleContradictionException("Every number field always sees at least one field: itself");
			}

			if(targetVisibleFields > maxGlobalVisibleFields) {
				throw new PuzzleContradictionException("Can not see more fields than the board allows");
			}

			// mark the number field itself as white
			know(pos, FieldKnowledge.White);

			// if the field is 1 by 1 we are already done
			if(width * height == 1) {
				return;
			}

			int[][] visibleCountSlotsTable = new int[DIRECTIONS.length][];
			int[] minVisibilityTable = new int[DIRECTIONS.length];

			// setup visibility into all directions
			for(int i = 0; i < DIRECTIONS.length; ++i) {
				Direction dir = DIRECTIONS[i];

				int maxVisibleFieldsIntoDir = Math.min(targetVisibleFields - 1, pos.fieldsToBorder(dir));
				int visibleFieldsIntoOtherDirs = maxGlobalVisibleFields - maxVisibleFieldsIntoDir;
				int minVis = minVisibilityTable[i] = Math.max(0, targetVisibleFields - visibleFieldsIntoOtherDirs);
				int[] visibleCountSlots = visibleCountSlotsTable[i] = new int[maxVisibleFieldsIntoDir + 1];


				// setup possible visibilities
				Position cur = pos;
				for (int j = 0; j <= maxVisibleFieldsIntoDir; ++j) {
					if (0 < j && j <= minVis) {
						// the field must be white
						know(cur, FieldKnowledge.White);
					}

					cur = cur.add(dir);

					if (j >= minVis && (!cur.isInField() || knowledge[cur.x][cur.y] != FieldKnowledge.White)) {
						// the field may be white

						// var is true <=> j visibility into the direction
						int var = visibleCountSlots[j] = newVar();

						if (cur.isInField()) {
							// var => cur.isBlack()
							when(var).then(cur.isBlack());
						}

						// if var is true, ensure that all fields between the number field and the wall are white
						Position no = pos;
						for (int k = 0; k < j; ++k) {
							no = no.add(dir);
							// var => no.isWhite()
							if(k >= minVis && knowledge[no.x][no.y] != FieldKnowledge.White) {
								when(var).then(no.isWhite());
							}
						}
					}
				}
			}

			// bind slot lists to binary encoded numbers, but only if they aro not exclusively zero
			Number[] nums = IntStream
					.range(0, DIRECTIONS.length)
					.filter(i -> visibleCountSlotsTable[i].length > 1 || minVisibilityTable[i] > 0)
					.mapToObj(i -> tieToNumber(visibleCountSlotsTable[i], minVisibilityTable[i]))
					.toArray(Number[]::new);

			if(nums.length == 0) {
				throw new PuzzleContradictionException("Proved that there is no possible correct visibility");
			}

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
			// only one possible value
			return new Constant(minNum);
		}
		// make sure at least one of the vars is true
		atLeastOneOf(Arrays.stream(visibleCountSlots).filter(var -> var > 0).toArray());
		Number result = new Number(maxNum);
		for(int num = minNum; num <= maxNum; ++num) {
			if(visibleCountSlots[num] > 0) {
				result.equalTo(new Constant(num), visibleCountSlots[num]);
			}
		}
		return result;
	}

	/**
	 * Ensures that every white field is connected to every other white field.
	 *
	 * Instead of proving the connectivity, this function creates rules that prove
	 * another property, which implies full-white-field-connectivity:
	 *   The non-existence of cycles and border-to-border connections of black fields.
	 *
	 * This is done by giving every black field, that needs an arrow (1.), exactly one
	 * arrow pointing to an adjacent black field (2.). A black field needs an arrow if it
	 * has two or more adjacent black fields or is directly located at the border of the board (1.).
	 * An arrow of a black field can not point to a black field that itself points back to the first field.
	 * A field adjacent to a border has to point into the border.
	 *
	 * This prevents border-to-border connections and double-cycles.
	 * It also gives simple cycles a rotation direction.
	 *
	 * To prevent simple cycles, every black field that needs an arrow must also have a number,
	 * which is one smaller than the black field's number, the arrow points to.
	 *
	 */
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

	// marks a position with a certain knowledge
	private void know(Position pos, FieldKnowledge knw) {
		if (knowledge[pos.x][pos.y] == FieldKnowledge.Unknown) {
			knowledge[pos.x][pos.y] = knw;
			addClause(knw == FieldKnowledge.White ? pos.isWhite() : pos.isBlack());
		} else if(knowledge[pos.x][pos.y] != knw) {
			throw new PuzzleContradictionException("Knowledge contradicts other knowledge");
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
			//e.printStackTrace();
			throw new PuzzleContradictionException("Logic contradiction detected");
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
