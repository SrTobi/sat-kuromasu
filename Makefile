test: compile
	java -cp kuromasu-1.0-deps.jar:. edu.kit.iti.formal.kuromasu.KuromasuTest
compile:
	javac -cp kuromasu-1.0-deps.jar MyKuromasuSolver.java
