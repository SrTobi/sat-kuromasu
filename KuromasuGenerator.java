import edu.kit.iti.formal.kuromasu.FieldValue;
import edu.kit.iti.formal.kuromasu.Kuromasu;
import edu.kit.iti.formal.kuromasu.Solution;

import java.io.*;
import java.nio.file.Files;
import java.util.*;

public class KuromasuGenerator {

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

		Position add(Direction other) {
			return new Position(this.x + other.dx, this.y + other.dy);
		}
		Position add(Position other) {
			return new Position(this.x + other.x, this.y + other.y);
		}


		private boolean isInField() {
			return 0 <= x && x < w
					&& 0 <= y && y < h;
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
				return dir.dy < 0 ? y : (h - 1) - y;
			} else {
				return dir.dx < 0 ? x : (w - 1) - x;
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
			return x * 13 + y * 101;
		}

		@Override
		public String toString() {
			return "P(" + x + ", " + y + ")";
		}
	}

	private static final Direction NORTH = new Direction(0, -1);
	private static final Direction SOUTH = new Direction(0, 1);
	private static final Direction WEST = new Direction(-1, 0);
	private static final Direction EAST = new Direction(1, 0);

	private static final Direction[] DIRECTIONS = new Direction[] {
			NORTH, SOUTH, WEST, EAST
	};

	int w, h;
	boolean[][] fields;

	KuromasuGenerator(int w, int h) {
		this.w = w;
		this.h = h;
		fields = new boolean[w][h];
	}

	int visibleFields(Position start) {
		int vfields = 1;
		for(Direction dir : DIRECTIONS) {
			Position pos = start.add(dir);

			while (pos.isInField() && !fields[pos.x][pos.y]) {
				pos = pos.add(dir);
				++vfields;
			}

		}
		return vfields;
	}

	boolean checkReachable() {
		Set<Position> whiteFields = new HashSet<>();

		Position start = null;
		for(int x = 0; x < w; ++x) {
			for(int y = 0; y < h; ++y) {
				if(!fields[x][y]) {
					Position p = new Position(x, y);
					whiteFields.add(p);
					if(start == null) {
						start = p;
					}
				}
			}
		}

		Queue<Position> q = new ArrayDeque<>();
		q.add(start);

		while (!q.isEmpty()) {
			Position cur = q.remove();
			for(Position n : cur.neighbours()) {
				if(whiteFields.remove(n)) {
					q.add(n);
				}
			}
		}

		return whiteFields.isEmpty();
	}

	void generate() {
		System.out.println("Generate " + w + "x" + h);

		Random rand = new Random();
		int blacks = rand.nextInt(w * h);
		int realBlacks = 0;

		for(int i = 0; i < blacks; ++i) {
			int x = rand.nextInt(w);
			int y = rand.nextInt(h);
			Position pos = new Position(x, y);
			if(!fields[x][y] && Arrays.stream(pos.neighbours()).noneMatch(f -> fields[f.x][f.y])) {
				fields[x][y] = true;
				if(!checkReachable()) {
					fields[x][y] = false;
				}else {
					++realBlacks;
				}
			}
		}

		int nums = rand.nextInt(w * h / 4);
		Map<Position, Integer> numFields = new HashMap<>();

		for(int i = 0; i < nums || numFields.isEmpty(); ++i) {
			int x = rand.nextInt(w);
			int y = rand.nextInt(h);
			Position pos = new Position(x, y);
			if(!fields[x][y] && !numFields.containsKey(pos)) {
				int vis = visibleFields(pos);
				numFields.put(pos, vis);
			}
		}

		System.out.println("  with " + realBlacks + "/" + blacks + " black fields and " + numFields.size() + "/" + nums + " number fields!");

		File file;

		do {
			file = new File("gen/sat." + w + "x" + h + "." + rand.nextInt() % 1000);
		}while (file.exists());

		// output
		try {
			PrintWriter out = new PrintWriter(file);
			out.println("w " + w);
			out.println("h " + h);

			numFields.forEach((pos, num) -> out.println("c " + pos.y + " " + pos.x + " " + num));
			out.close();

			Kuromasu game = Kuromasu.load(file);
			Solution sol = new Solution(game);
			for(int x = 0; x < w; ++x) {
				for(int y = 0; y < h; ++y) {
					sol.setField(y, x, fields[x][y]? FieldValue.BLACK : FieldValue.WHITE);
				}
			}

			if(sol.isValid()) {
				System.out.println("Found valid!");
				sol.print();
			}else {
				System.out.println("Found invalid!");
				Files.delete(file.toPath());
			}

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) {
		Random rand = new Random();
		for(int i = 0; i < 20; ++i) {
			KuromasuGenerator gen = new KuromasuGenerator(rand.nextInt(40) + 2, rand.nextInt(40) + 2);
			gen.generate();
		}
	}
}
