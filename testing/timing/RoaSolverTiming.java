import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;

import edu.princeton.cs.roasolver.RoaSolver;
import edu.princeton.cs.roasolver.RoaSolver.RoaSolverInput;
import edu.princeton.cs.roasolver.RoaSolver.RoaSolverOutput;

// runs automated performance tests for RoaSolver
public class RoaSolverTiming {

    // encapsulates the data for trials with the same parameters
    private static class TimingData {

        public int b; // number of bidder classes
        public int m; // number of items
        public int c; // number of types

        public int T; // number of trials

        public int soCount; // total number of times the separation oracle is run across all trials
        public long runTime; // total runtime across all trials

        // simple constructor
        public TimingData(int b, int m, int c, int T, int soCount, long runTime) {

            this.b = b;
            this.m = m;
            this.c = c;
            this.T = T;
            this.soCount = soCount;
            this.runTime = runTime;
        }

        // header for csv output
        public static final String headerString = "b,m,c,T,#variables,#constraints,socount,time";

        // returns string representation for a row of csv output
        public String toString() {

            int variables = (m * b * c) + (b * c);
            int constraints = (2 * m * b * c) + (b * c) + (b * c * c);

            return b + "," + m + "," + c + "," + T + "," + variables + "," + constraints + "," + (soCount / (double) T) + ","
                    + (runTime / 1e9d / T);
        }
    }

    // parses the given string as a list of range of ints
    // the list is delimited by semicolons
    // each range of ints is either x~y or x (e.g. 1~2 or 3)
    private static int[] intRangeList(String list) throws Exception {

        ArrayList<Integer> rangeList = new ArrayList<Integer>();

        String[] tokens = list.split(";");

        for (String token : tokens) {

            String[] values = token.split("~");

            if (values.length < 1 || values.length > 2) {

                throw new Exception("Invalid range!");
            }

            int[] bounds = new int[2];
            bounds[0] = Integer.parseInt(values[0]);
            bounds[1] = Integer.parseInt(values[values.length == 1 ? 0 : 1]);

            for (int yi = bounds[0]; yi <= bounds[1]; yi++) {

                rangeList.add(yi);
            }
        }

        int y = rangeList.size();
        int[] ints = new int[y];
        for (int yi = 0; yi < y; yi++) {

            ints[yi] = rangeList.get(yi);
        }

        return ints;
    }

    // body of testing code!
    public static void main(String[] args) throws IOException {

        if (args.length != 5) {

            System.err.println("usage: java RoaSolverTest <n> <m> <c> <T> <filename>");
            return;
        }
        
        int[] bs; // all values for b
        int[] ms; // all values for m
        int[] cs; // all values for c

        int T; // number of iterations for each unique (b, m, c)

        String fileName; // full file name to write to

        // parse inputs
        try {

            bs = intRangeList(args[0]);
            ms = intRangeList(args[1]);
            cs = intRangeList(args[2]);
            T = Integer.parseInt(args[3]);
            fileName = args[4];
        } catch (Exception e) {

            System.err.println("Error parsing arguments");
            System.err.println(e);
            return;
        }

        // open file for writing
        FileWriter fileWriter = new FileWriter(fileName);
        PrintWriter out = new PrintWriter(fileWriter);

        out.println(TimingData.headerString);
        System.out.println(TimingData.headerString);
        out.flush();

        // iterate through possible parameters
        for (int b : bs) {
            for (int m : ms) {
                for (int c : cs) {

                    TimingData timingData = new TimingData(b, m, c, T, 0, 0);

                    // run each trial
                    for (int t = 0; t < T; t++) {

                        // random number of bidders per bidder class
                        int[] n_b = new int[b];
                        for (int bi = 0; bi < b; bi++) {

                            n_b[bi] = (int) (Math.random() * b) + 1;
                        }

                        // assume same type class per type
                        int[] t_c = new int[c];
                        for (int ci = 0; ci < c; ci++) {

                            t_c[ci] = 0;
                        }

                        // generate random values for p_bc
                        double[][] p_bc = new double[b][c];
                        for (int bi = 0; bi < b; bi++) {

                            double rowSum = 0.0;

                            for (int ci = 0; ci < c; ci++) {

                                p_bc[bi][ci] = Math.random();
                                rowSum += p_bc[bi][ci];
                            }

                            // normalize
                            for (int ci = 0; ci < c; ci++) {

                                p_bc[bi][ci] /= rowSum;
                            }
                        }

                        // generate random values for v_cm
                        double[][] v_cm = new double[c][m];
                        for (int ci = 0; ci < c; ci++) {
                            for (int mi = 0; mi < m; mi++) {

                                v_cm[ci][mi] = Math.random();
                            }
                        }

                        // solve and accumulate
                        try {

                            RoaSolverInput input = new RoaSolverInput(b, m, c, n_b, t_c, p_bc, v_cm);
                            RoaSolver solver = new RoaSolver(input);
                            RoaSolverOutput output = solver.getOutput();

                            timingData.soCount += output.soCount;
                            timingData.runTime += output.runTime;
                        } catch (Exception e) {

                            System.err.println(e);
                        }
                    }
                    
                    // print results of trials
                    out.println(timingData);
                    System.out.println(timingData);
                    out.flush();
                }
            }
        }

        out.close();
    }
}