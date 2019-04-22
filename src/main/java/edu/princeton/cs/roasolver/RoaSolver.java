package edu.princeton.cs.roasolver;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Formatter;
import java.util.NoSuchElementException;
import java.util.PriorityQueue;
import java.util.Scanner;

import ilog.concert.*;
import ilog.cplex.*;

// finds the revenue-optimal auction!
public class RoaSolver {

    // input parameters
    private final int b; // number of bidder classes
    private final int m; // number of items
    private final int c; // number of types

    private final int[] n_b; // n_b[bi] = number of bidders in bidder class bi
    private final int[] t_c; // t_c[ci] = type class for type ci
    private final double[][] p_bc; // p_bc[bi][ci] = probability for a bidder in bidder class bi to have type ci
    private final double[][] v_cm; // v_cm[ci][mi] = value of item mi for type ci

    // solver
    private final IloCplex cplex; // cplex instance
    private final IloNumVar[][][] pi_bcm; // pi_bcm[bi][ci][mi] = interim probability for a bidder in bidder class bi to
                                          // get item mi when reporting type ci
    private final IloNumVar[][] q_bc; // q_bc[bi][ci] = interim expected price a bidder in bidder class bi pays when
                                      // reporting type ci

    // solution to be output
    private final double[][][] pi_sol_bcm;
    private final double[][] q_sol_bc;

    // timing in nanoseconds
    private final long startTime;
    private final long endTime;
    private final long runTime;

    // encapsulates all internal exceptions
    public static class RoaSolverError extends Exception {

        // required by Java
        private static final long serialVersionUID = 1L;

        public RoaSolverError(String message) {

            super(message);
        }
    }

    // encapsulates the input needed for a trial
    public static class RoaSolverInput {

        public final int b; // number of bidder classes
        public final int m; // number of items
        public final int c; // number of types

        public final int[] n_b; // n_b[bi] = number of bidders in bidder class bi
        public final int[] t_c; // t_c[ci] = type class for type ci
        public final double[][] p_bc; // p_bc[bi][ci] = probability for a bidder in bidder class bi to have type ci
        public final double[][] v_cm; // v_cm[ci][mi] = value of item mi for type ci

        // simple constructor
        public RoaSolverInput(int b, int m, int c, int[] n_b, int[] t_c, double[][] p_bc, double[][] v_cm) {

            this.b = b;
            this.m = m;
            this.c = c;

            this.n_b = n_b;
            this.t_c = t_c;
            this.p_bc = p_bc;
            this.v_cm = v_cm;
        }

        // generates the inputs for all trials by expanding all type classes and
        // multiplicity profiles from the given parser
        public static RoaSolverInput[] getInputs(RoaSolverParser parser) {

            // first half: expand all type classes to explicit types

            // temporary variables to iteratively build p_bc, v_cm, t_c
            ArrayList<Integer> t_temp_c = new ArrayList<Integer>(); // to build t_c
            ArrayList<double[]> p_temp_cb = new ArrayList<double[]>(); // to build p_bc
            ArrayList<double[]> v_temp_cm = new ArrayList<double[]>(); // to build v_cm

            // expand each type class in turn
            for (int ti = 0; ti < parser.t; ti++) {

                // iterate through the items, building up the types and the associated
                // probabilities

                // contains the incomplete types from expanding the items seen so far
                // each element is an incomplete type (up to m values, one for each item seen so
                // far)
                ArrayList<double[]> v_curr_ym = new ArrayList<double[]>();

                // contains the probabilities for the corresponding incomplete type
                // each element is the probability conditioned on being in this type class
                ArrayList<Double> p_curr_y = new ArrayList<Double>();

                // base case: empty type with (conditional) certainty
                v_curr_ym.add(new double[parser.m]); // empty type
                p_curr_y.add(1.0); // full conditional probability

                // iterate through items
                for (int mi = 0; mi < parser.m; mi++) {

                    // incomplete types at next iteration
                    ArrayList<double[]> v_next_ym = new ArrayList<double[]>();
                    ArrayList<Double> p_next_y = new ArrayList<Double>();

                    // for every incomplete type so far...
                    int y = v_curr_ym.size();
                    for (int yi = 0; yi < y; yi++) {

                        // get the incomplete type and associated probability
                        double[] v_curr_m = v_curr_ym.get(yi);
                        double p_curr = p_curr_y.get(yi);

                        // case 1: this type class uses a single value for this item
                        if (parser.d_mt[mi][ti].charAt(0) != 'D') {

                            // copy previous incomplete type
                            double[] v_next_m = v_curr_m;
                            double p_next = p_curr;

                            // update the incomplete type by adding an entry for this item
                            // (only one possible updated type so we just override the old array)
                            v_next_m[mi] = Double.parseDouble(parser.d_mt[mi][ti]);

                            // add updated incomplete type to collection
                            v_next_ym.add(v_next_m);
                            p_next_y.add(p_next);
                        }

                        // case 2: this type class uses a valuation distribution for this item
                        else {

                            // the valuation distribution used
                            int ri = Integer.parseInt(parser.d_mt[mi][ti].substring(1)) - 1;

                            // go through all possible values/probabilities for this item (in the support)
                            for (int si = 0; si < parser.s; si++) {

                                // skip impossible values for this valuation distribution
                                if (parser.phi_rs[ri][si] == 0.0)
                                    continue;

                                // copy previous incomplete type
                                double[] v_next_m = v_curr_m.clone();
                                double p_next = p_curr;

                                // update the incomplete type by adding an entry for this item
                                v_next_m[mi] = parser.u_s[si];
                                p_next *= parser.phi_rs[ri][si];

                                // add updated incomplete type to collection
                                v_next_ym.add(v_next_m);
                                p_next_y.add(p_next);
                            }
                        }

                        // finished iterating through this incomplete type
                    }

                    // finished iterating through this item, so update and continue
                    v_curr_ym = v_next_ym;
                    p_curr_y = p_next_y;
                }

                // finished calculating all types and probabilities for this type class

                // now iterate through each type in this type class and expand
                int y = v_curr_ym.size();
                for (int yi = 0; yi < y; yi++) {

                    // type and associated probability
                    double[] v_m = v_curr_ym.get(yi);
                    double p = p_curr_y.get(yi);

                    // actual probabilities for this type (removing conditioning on being from this
                    // type class)
                    double[] p_b = new double[parser.b];
                    for (int bi = 0; bi < parser.b; bi++) {

                        p_b[bi] = p * parser.p_bt[bi][ti];
                    }

                    // add these types and probabilities to the collections
                    t_temp_c.add(ti);
                    p_temp_cb.add(p_b);
                    v_temp_cm.add(v_m);
                }

                // finished with this type class
            }

            // finished with expanding all type classes

            // calculate c, t_c, p_bc, v_cm

            int c = p_temp_cb.size();

            int[] t_c = new int[c];
            for (int ci = 0; ci < c; ci++) {
                t_c[ci] = t_temp_c.get(ci);
            }

            double[][] p_bc = new double[parser.b][c];
            for (int bi = 0; bi < parser.b; bi++) {
                for (int ci = 0; ci < c; ci++) {
                    p_bc[bi][ci] = p_temp_cb.get(ci)[bi];
                }
            }

            double[][] v_cm = new double[c][parser.m];
            for (int ci = 0; ci < c; ci++) {
                for (int mi = 0; mi < parser.m; mi++) {
                    v_cm[ci][mi] = v_temp_cm.get(ci)[mi];
                }
            }

            // second half: expand all possible multiplicity profiles

            // iterate through the bidder classes, building up the multiplicity profiles

            // contains the multiplicity profiles from expanding the bidder classes so far
            // each element is an incomplete multiplicity profile (up to b values, one for
            // each bidder class seen so far)
            ArrayList<int[]> n_curr_yb = new ArrayList<int[]>();

            // base case: empty multiplicity profile
            n_curr_yb.add(new int[parser.b]);

            // iterate through each bidder class
            for (int bi = 0; bi < parser.b; bi++) {

                // multiplicity profiles at next iteration
                ArrayList<int[]> n_next_yb = new ArrayList<int[]>();

                // for every incomplete multiplicity profile so far...
                int y = n_curr_yb.size();
                for (int yi = 0; yi < y; yi++) {

                    // get the current incomplete multiplicity profile
                    int[] n_curr_b = n_curr_yb.get(yi);

                    // go through all possible multiplicities for this bidder class
                    int z = parser.n_bz[bi].length;
                    for (int zi = 0; zi < z; zi++) {

                        // copy previous incomplete multiplicity profile
                        int[] n_next_b = n_curr_b.clone();

                        // update the incomplete multiplicity profile by adding a multiplicity for this
                        // bidder class
                        n_next_b[bi] = parser.n_bz[bi][zi];

                        // add updated multiplicity profile to the collection
                        n_next_yb.add(n_next_b);
                    }
                }

                // finished iterating through this bidder class, so update and continue
                n_curr_yb = n_next_yb;
            }

            // finished calculating all multiplicity profiles

            // finally: return all possible outputs
            int y = n_curr_yb.size();
            RoaSolverInput[] inputs = new RoaSolverInput[y];
            for (int yi = 0; yi < y; yi++) {
                inputs[yi] = new RoaSolverInput(parser.b, parser.m, c, n_curr_yb.get(yi), t_c, p_bc, v_cm);
            }

            return inputs;
        }
    }

    // encapsulates the output from a trial
    public static class RoaSolverOutput {

        // input parameters
        public final int b; // number of bidder classes
        public final int m; // number of items
        public final int c; // number of types

        public final int[] n_b; // n_b[bi] = number of bidders in bidder class bi
        public final int[] t_c; // t_c[ci] = type class for type ci
        public final double[][] p_bc; // p_bc[bi][ci] = probability for a bidder in bidder class bi to have type ci
        public final double[][] v_cm; // v_cm[ci][mi] = value of item mi for type ci

        // solution
        public final double J; // expected revenue
        public final double[][][] pi_bcm; // pi_bcm[bi][ci][mi] = interim probability for a bidder in bidder class bi to
                                          // get item mi when reporting type ci
        public final double[][] q_bc; // q_bc[bi][ci] = interim expected price a bidder in bidder class bi pays when
                                      // reporting type ci

        // timing
        public final long runTime; // how long the trial ran for, in nanoseconds

        // simple constructor
        public RoaSolverOutput(int b, int m, int c, int[] n_b, int[] t_c, double[][] p_bc, double[][] v_cm, double J,
                double[][][] pi_bcm, double[][] q_bc, long runTime) {

            this.b = b;
            this.m = m;
            this.c = c;

            this.n_b = n_b;
            this.t_c = t_c;
            this.p_bc = p_bc;
            this.v_cm = v_cm;

            this.J = J;
            this.pi_bcm = pi_bcm;
            this.q_bc = q_bc;

            this.runTime = runTime;
        }

        // a string representation of the problem and solution, suitable for printing to
        // the terminal
        public String toFullText() {

            StringBuilder sb = new StringBuilder();
            Formatter f = new Formatter(sb);

            // explicit problem statement

            f.format("%d %d %d\n", b, m, c);

            for (int ci = 0; ci < c; ci++) {

                if (ci != 0)
                    f.format(" ");

                f.format("%8d", t_c[ci] + 1);
            }

            f.format("\n");

            for (int bi = 0; bi < b; bi++) {

                for (int ci = 0; ci < c; ci++) {

                    if (ci != 0)
                        f.format(" ");

                    f.format("%8.4f", p_bc[bi][ci]);
                }

                f.format(" %d\n", n_b[bi]);
            }

            for (int mi = 0; mi < m; mi++) {

                for (int ci = 0; ci < c; ci++) {

                    if (ci != 0)
                        f.format(" ");

                    f.format("%8.4f", v_cm[ci][mi]);
                }

                f.format("\n");
            }

            // solution

            f.format("\n\n%8.4f\n", J);

            for (int bi = 0; bi < b; bi++) {

                f.format("\n");

                for (int mi = 0; mi < m; mi++) {

                    for (int ci = 0; ci < c; ci++) {

                        if (ci != 0)
                            f.format(" ");

                        f.format("%8.4f", pi_bcm[bi][ci][mi]);
                    }

                    f.format("\n");
                }

                for (int ci = 0; ci < c; ci++) {

                    if (ci != 0)
                        f.format(" ");

                    f.format("%8.4f", q_bc[bi][ci]);
                }

                f.format("\n");
            }

            f.format("\n");
            f.format("%8.4f\n", runTime / 1e9d);
            f.format("\n");
            f.format("\n");

            f.close();

            return sb.toString();
        }

        // a string representation of the problem and solution, suitable for viewing as
        // a CSV file
        public String toFullCSV() {

            StringBuilder sb = new StringBuilder();

            // explicit problem statement

            sb.append(b);
            sb.append(',');
            sb.append(m);
            sb.append(',');
            sb.append(c);
            sb.append('\n');

            for (int ci = 0; ci < c; ci++) {

                sb.append(ci == 0 ? "" : ',');
                sb.append(t_c[ci] + 1);
            }

            sb.append('\n');

            for (int bi = 0; bi < b; bi++) {

                for (int ci = 0; ci < c; ci++) {

                    sb.append(ci == 0 ? "" : ',');
                    sb.append(p_bc[bi][ci]);
                }

                sb.append(',');
                sb.append(n_b[bi]);
                sb.append('\n');
            }

            for (int mi = 0; mi < m; mi++) {

                for (int ci = 0; ci < c; ci++) {

                    sb.append(ci == 0 ? "" : ',');
                    sb.append(v_cm[ci][mi]);
                }

                sb.append('\n');
            }

            sb.append('\n');
            sb.append('\n');

            // solution

            sb.append(J);
            sb.append('\n');

            for (int bi = 0; bi < b; bi++) {

                sb.append('\n');

                for (int mi = 0; mi < m; mi++) {

                    for (int ci = 0; ci < c; ci++) {

                        sb.append(ci == 0 ? "" : ',');
                        sb.append(pi_bcm[bi][ci][mi]);
                    }

                    sb.append('\n');
                }

                for (int ci = 0; ci < c; ci++) {

                    sb.append(ci == 0 ? "" : ',');
                    sb.append(q_bc[bi][ci]);
                }

                sb.append('\n');
            }

            sb.append('\n');
            sb.append(runTime / 1e9d);
            sb.append('\n');

            return sb.toString();
        }

        // a string representation of only the bidder counts and the expected revenue,
        // suitable for printing to the terminal
        public String toBriefText() {

            StringBuilder sb = new StringBuilder();
            Formatter f = new Formatter(sb);

            for (int bi = 0; bi < b; bi++) {

                f.format("%8d ", n_b[bi]);
            }

            f.format("%8.4f ", J);
            f.format("%8.4f\n", runTime / 1e9f);

            f.close();

            return sb.toString();
        }

        // a string representation of only the bidder counts and the expected revenue,
        // suitable for viewing as a CSV file
        public String toBriefCSV() {

            StringBuilder sb = new StringBuilder();

            for (int bi = 0; bi < b; bi++) {

                sb.append(n_b[bi]);
                sb.append(',');
            }

            sb.append(J);
            sb.append(',');
            sb.append(runTime / 1e9f);
            sb.append('\n');

            return sb.toString();
        }

        // a string identifying this output, for use in file names
        public String toID() {

            StringBuilder sb = new StringBuilder();

            for (int bi = 0; bi < b; bi++) {

                sb.append('_');
                sb.append(n_b[bi]);
            }

            return sb.toString();
        }
    }

    // helper class to parse, validate, and normalize input
    public static class RoaSolverParser {

        // parsing location
        private final Scanner sc; // scanner to draw input from
        private int lineNumber = 0; // number of lines seen so far
        private String[] lineTokens; // all the tokens in the current line
        private int index; // index of current token in in lineTokens

        // parsed inputs
        public final int b; // number of bidder classes
        public final int m; // number of items
        public final int t; // number of type classes
        public final int r; // number of valuation distributions
        public final int s; // number of values in the support of the valuation distributions

        public final int[][] n_bz; // n_bz[bi][zi] possible number of bidders in bidder class bi
        public final double[][] p_bt; // p_bt[bi][ti] = (normalized) prob. for bidder class bi to have type class ti
        public final String[][] d_mt; // d_mt[mi][ti] = valuation distribution that type class ti has for item mi
        public final double[][] phi_rs; // phi_rs[li][si] = (normalized) prob. that valuation distribution li draws
                                        // value u_s[si]
        public final double[] u_s; // u_s[si] = value si in the support of the valuation distributions

        // advances scanner to next line
        private void nextLine() throws RoaSolverError {

            try {

                lineNumber++;
                lineTokens = sc.nextLine().trim().split("\\s+");
                index = 0;

            } catch (NoSuchElementException e) {
                throw new RoaSolverError(String.format("Cannot find line %d!", lineNumber));
            }
        }

        // checks that a line is complete
        private void endLine() {

            if (index < lineTokens.length)
                System.err.printf("Warning: line %d of input has %d unused tokens!\n", lineNumber,
                        lineTokens.length - index);

            index = lineTokens.length;
        }

        // parses the next token as a double
        private double nextDouble(String id) throws RoaSolverError {

            try {
                return Double.parseDouble(lineTokens[index++]);
            } catch (NumberFormatException e) {
                throw new RoaSolverError(
                        String.format("Error parsing %s (line %d, token %d) as a double", id, lineNumber, index));
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new RoaSolverError(String.format("Cannot find %s: line %d is too short!", id, lineNumber));
            }
        }

        // parses the next token as an int
        private int nextInt(String id) throws RoaSolverError {

            try {
                return Integer.parseInt(lineTokens[index++]);
            } catch (NumberFormatException e) {
                throw new RoaSolverError(
                        String.format("Error parsing %s (line %d, token %d) as an integer", id, lineNumber, index));
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new RoaSolverError(String.format("Cannot find %s: line %d is too short!", id, lineNumber));
            }
        }

        // parses the next token as a list of range of ints
        // the list is delimited by semicolons
        // each range of ints is either x~y or x (e.g. 1~2 or 3)
        private int[] nextIntRangeList(String id) throws RoaSolverError {

            try {

                ArrayList<Integer> rangeList = new ArrayList<Integer>();

                String[] tokens = lineTokens[index++].split(";");

                for (String token : tokens) {

                    String[] values = token.split("~");

                    if (values.length < 1 || values.length > 2)
                        throw new RoaSolverError(
                                String.format("Error parsing %s (line %d, token %d) as a valid integer range list", id,
                                        lineNumber, index));

                    int[] bounds = new int[2];
                    bounds[0] = Integer.parseInt(values[0]);
                    bounds[1] = Integer.parseInt(values[values.length == 1 ? 0 : 1]);

                    if (bounds[0] > bounds[1])
                        throw new RoaSolverError(
                                String.format("Error parsing %s (line %d, token %d) as a valid integer range list", id,
                                        lineNumber, index));

                    for (int yi = bounds[0]; yi <= bounds[1]; yi++) {

                        rangeList.add(yi);
                    }
                }

                int y = rangeList.size();
                int[] next = new int[y];
                for (int yi = 0; yi < y; yi++) {

                    next[yi] = rangeList.get(yi);
                }

                return next;

            } catch (NumberFormatException e) {
                throw new RoaSolverError(String.format(
                        "Error parsing %s (line %d, token %d) as a valid integer range list", id, lineNumber, index));
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new RoaSolverError(String.format("Cannot find %s: line %d is too short!", id, lineNumber));
            }
        }

        // parses the next token as a String
        private String nextString(String id) throws RoaSolverError {

            try {
                return lineTokens[index++];
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new RoaSolverError(String.format("Cannot find %s: line %d is too short!", id, lineNumber));
            }
        }

        // validates bounds on b, m, t, r, s
        private void validateFirstRow() throws RoaSolverError {

            if (b < 1)
                throw new RoaSolverError("b must be at least 1"); // bad_00.txt
            if (m < 1)
                throw new RoaSolverError("m must be at least 1"); // bad_01.txt
            if (t < 1)
                throw new RoaSolverError("t must be at least 1"); // bad_02.txt
            if (r < 0)
                throw new RoaSolverError("r must be at least 0"); // bad_03.txt
            if (s < 0)
                throw new RoaSolverError("s must be at least 0"); // bad_04.txt
        }

        // validates bounds on n_b, p_bt, d_mt, phi_rs, u_s
        private void validate() throws RoaSolverError {

            // validate contents of n_b
            int n = 0;

            for (int bi = 0; bi < b; bi++) {

                int z = n_bz[bi].length;

                if (z < 1)
                    throw new RoaSolverError(String.format("n_%d cannot be empty", bi + 1));

                int min = Integer.MAX_VALUE;

                for (int zi = 0; zi < z; zi++) {

                    if (n_bz[bi][zi] < 0)
                        throw new RoaSolverError(String.format("n_%d must have a lower bound of at least 0", bi + 1)); // bad_05.txt

                    if (n_bz[bi][zi] < min)
                        min = n_bz[bi][zi];
                }

                n += min;
            }

            if (n < 1)
                throw new RoaSolverError("sum_i n_i must have a lower bound of at least 1"); // bad_06.txt

            // validate contents of p_bt
            for (int bi = 0; bi < b; bi++) {

                double rowSum = 0.0;

                for (int ti = 0; ti < t; ti++) {

                    if (p_bt[bi][ti] < 0.0)
                        throw new RoaSolverError(String.format("p_{%d,%d} must be nonnegative", bi + 1, ti + 1)); // bad_07.txt

                    rowSum += p_bt[bi][ti];
                }

                if (rowSum <= 0.0)
                    throw new RoaSolverError(String.format("sum_i p_{%d,i} must be positive", bi + 1)); // bad_08.txt
            }

            // validate contents of d_mt
            for (int mi = 0; mi < m; mi++) {

                for (int ti = 0; ti < t; ti++) {

                    // safety check, should be impossible
                    if (d_mt[mi][ti].length() < 1)
                        throw new RoaSolverError(String.format("d_{%d,%d} must be nonempty", mi + 1, ti + 1));

                    // if valuation distribution is specified
                    if (d_mt[mi][ti].charAt(0) == 'D') {

                        try {

                            int li = Integer.parseInt(d_mt[mi][ti].substring(1));

                            if (li < 1 || r < li)
                                throw new RoaSolverError(String
                                        .format("d_{%d,%d} is not a valid valuation distribution", mi + 1, ti + 1)); // bad_09.txt
                        }

                        catch (NumberFormatException e) {

                            throw new RoaSolverError(
                                    String.format("d_{%d,%d} is not a valuation distribution", mi + 1, ti + 1)); // bad_10.txt
                        }

                        continue;
                    }

                    // special case: should be float
                    try {

                        Double.parseDouble(d_mt[mi][ti]);
                    }

                    catch (NumberFormatException e) {

                        throw new RoaSolverError(String.format("d_{%d,%d} is not a valid float", mi + 1, ti + 1)); // bad_11.txt
                    }
                }
            }

            // validate contents of phi_rs
            for (int li = 0; li < r; li++) {

                double rowSum = 0.0;

                for (int si = 0; si < s; si++) {

                    if (phi_rs[li][si] < 0.0)
                        throw new RoaSolverError(String.format("r_{%d,%d} must be nonnegative", li + 1, si + 1)); // bad_12.txt

                    rowSum += phi_rs[li][si];
                }

                if (rowSum <= 0.0)
                    throw new RoaSolverError(String.format("sum_i r_{%d,i} must be positive", li + 1)); // bad_13.txt
            }

            // validate the contents of u_s
            /* nothing to validate */
        }

        // normalizes p_bt, phi_rs
        private void normalize() {

            // normalize p_bt
            for (int bi = 0; bi < b; bi++) {

                double rowSum = 0.0;

                for (int ti = 0; ti < t; ti++) {

                    rowSum += p_bt[bi][ti];
                }

                for (int ti = 0; ti < t; ti++) {

                    p_bt[bi][ti] /= rowSum;
                }
            }

            // normalize phi_rs
            for (int ri = 0; ri < r; ri++) {

                double rowSum = 0.0;

                for (int si = 0; si < s; si++) {

                    rowSum += phi_rs[ri][si];
                }

                for (int si = 0; si < s; si++) {

                    phi_rs[ri][si] /= rowSum;
                }
            }
        }

        // parses, validates, and normalizes input
        public RoaSolverParser(Scanner sc) throws RoaSolverError {

            // save scanner
            this.sc = sc;
            nextLine();

            // first row
            b = nextInt("b");
            m = nextInt("m");
            t = nextInt("t");
            r = nextInt("l");
            s = nextInt("s");
            endLine();

            validateFirstRow();

            n_bz = new int[b][];
            p_bt = new double[b][t];
            d_mt = new String[m][t];
            phi_rs = new double[r][s];
            u_s = new double[s];

            // first matrix (p_bt, n_bz)
            for (int bi = 0; bi < b; bi++) {

                nextLine();

                for (int ti = 0; ti < t; ti++) {

                    p_bt[bi][ti] = nextDouble(String.format("p_{%d,%d}", bi + 1, ti + 1));
                }

                n_bz[bi] = nextIntRangeList(String.format("n_%d", bi + 1));
                endLine();
            }

            // second matrix (d_mt)
            for (int mi = 0; mi < m; mi++) {

                nextLine();

                for (int ti = 0; ti < t; ti++) {

                    d_mt[mi][ti] = nextString(String.format("d_{%d,%d}", mi + 1, ti + 1));
                }

                endLine();
            }

            // third matrix (phi_rs)
            for (int ri = 0; ri < r; ri++) {

                nextLine();

                for (int si = 0; si < s; si++) {

                    phi_rs[ri][si] = nextDouble(String.format("r_{%d,%d}", ri + 1, si + 1));
                }

                endLine();
            }

            // last row (u_s)
            if (s > 0) {

                nextLine();

                for (int si = 0; si < s; si++) {

                    u_s[si] = nextDouble(String.format("u_%d", si + 1));
                }

                endLine();
            }

            validate();
            normalize();
            sc.close();
        }

        // returns the heading line for printing to the terminal
        public String getBriefTextHeading() {

            StringBuilder sb = new StringBuilder();

            for (int bi = 0; bi < b; bi++) {

                String name = "     n_" + (bi + 1) + " ";
                name = name.substring(name.length() - 9);

                sb.append(name);
            }

            sb.append("     rev ");
            sb.append("    time\n");

            return sb.toString();
        }

        // returns the heading line for viewing as a CSV file
        public String getBriefCSVHeading() {

            StringBuilder sb = new StringBuilder();

            for (int bi = 0; bi < b; bi++) {

                sb.append("n_" + (bi + 1) + ",");
            }

            sb.append("rev,");
            sb.append("time\n");

            return sb.toString();
        }
    }

    // creates and solves a trial from the given input
    public RoaSolver(RoaSolverInput in) throws RoaSolverError, IloException {

        startTime = System.nanoTime();

        // instantiate input parameters
        this.b = in.b;
        this.m = in.m;
        this.c = in.c;

        this.n_b = in.n_b;
        this.t_c = in.t_c;
        this.p_bc = in.p_bc;
        this.v_cm = in.v_cm;

        // instantiate cplex instance
        this.cplex = new IloCplex();
        this.pi_bcm = new IloNumVar[b][c][m];
        this.q_bc = new IloNumVar[b][c];

        // shh, quiet!
        cplex.setOut(null);
        cplex.setWarning(null);

        // instantiate solutions
        pi_sol_bcm = new double[b][c][m];
        q_sol_bc = new double[b][c];

        // solve!
        solve();

        // calculate timing
        endTime = System.nanoTime();
        runTime = endTime - startTime;
    }

    // returns the output from the solution
    public RoaSolverOutput getOutput() throws RoaSolverError {

        try {

            double J = cplex.getObjValue();
            return new RoaSolverOutput(b, m, c, n_b, t_c, p_bc, v_cm, J, pi_sol_bcm, q_sol_bc, runTime);

        } catch (IloException e) {
            throw new RoaSolverError("Cannot obtain objective value!");
        }
    }

    // sets up the cplex model and solves it
    private void solve() throws IloException {

        // create the variables for pi_bcm
        for (int bi = 0; bi < b; bi++) {
            for (int ci = 0; ci < c; ci++) {
                for (int mi = 0; mi < m; mi++) {
                    String name = "pi_" + (bi + 1) + "_" + (ci + 1) + "_" + (mi + 1);
                    pi_bcm[bi][ci][mi] = cplex.numVar(0.0, 1.0, name);
                }
            }
        }

        // create the variables for q_
        for (int bi = 0; bi < b; bi++) {
            for (int ci = 0; ci < c; ci++) {
                String name = "q_" + (bi + 1) + "_" + (ci + 1);
                q_bc[bi][ci] = cplex.numVar(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, name);
            }
        }

        // define the model with constraints, objective, and separation oracle
        addIRConstraints();
        addBICConstraints();
        addObjective();
        addSO();

        // execute cplex solver
        cplex.solve();

        // extract solution for pi_bcm
        for (int bi = 0; bi < b; bi++) {
            for (int ci = 0; ci < c; ci++) {
                for (int mi = 0; mi < m; mi++) {
                    pi_sol_bcm[bi][ci][mi] = cplex.getValue(pi_bcm[bi][ci][mi]);
                }
            }
        }

        // extract solution for q_sol
        for (int bi = 0; bi < b; bi++) {
            for (int ci = 0; ci < c; ci++) {
                q_sol_bc[bi][ci] = cplex.getValue(q_bc[bi][ci]);
            }
        }
    }

    // adds constraints to ensure that the mechanism is interim IR:
    // for each bi, ci, we ensure that
    // sum_{mi} (v_cm[ci][mi] * pi_bcm[bi][ci][mi]) - q_bc[bi][ci] >= 0
    private void addIRConstraints() throws IloException {

        for (int bi = 0; bi < b; bi++) {
            for (int ci = 0; ci < c; ci++) {

                double[] v_m = v_cm[ci];
                IloNumVar[] pi_m = pi_bcm[bi][ci];
                IloNumVar q = q_bc[bi][ci];

                cplex.addGe(cplex.scalProd(v_m, pi_m), q);
            }
        }
    }

    // adds constraints to ensure that the mechanism is BIC:
    // for each bi, ci1, ci2, we ensure that
    // sum_{mi} (v_cm[ci1][mi] * pi_bcm[bi][ci1][mi]) - q_bc[bi][ci1] >= sum_{mi}
    // (v_cm[ci1][mi] * pi_bcm[bi][ci2][mi]) - q_bc[bi][ci2]
    private void addBICConstraints() throws IloException {

        for (int bi = 0; bi < b; bi++) {
            for (int ci1 = 0; ci1 < c; ci1++) {

                double[] v_m = v_cm[ci1];
                IloNumVar[] pi1_m = pi_bcm[bi][ci1];
                IloNumVar q1 = q_bc[bi][ci1];

                IloNumExpr expr1 = cplex.diff(cplex.scalProd(v_m, pi1_m), q1);

                for (int ci2 = 0; ci2 < c; ci2++) {

                    if (ci2 == ci1)
                        continue;

                    IloNumVar[] pi2_m = pi_bcm[bi][ci2];
                    IloNumVar q2 = q_bc[bi][ci2];

                    IloNumExpr expr2 = cplex.diff(cplex.scalProd(v_m, pi2_m), q2);

                    cplex.addGe(expr1, expr2);
                }
            }
        }
    }

    // adds the objective function:
    // maximize the expected revenue given by
    // sum_{bi, ci} (n_b[bi] * q_bc[bi][ci] * p_bc[bi][ci])
    private void addObjective() throws IloException {

        IloNumExpr[] prods_b = new IloNumExpr[b];

        for (int bi = 0; bi < b; bi++) {

            double[] p_c = p_bc[bi];
            IloNumVar[] q_c = q_bc[bi];
            double n = n_b[bi];

            prods_b[bi] = cplex.prod(n, cplex.scalProd(q_c, p_c));
        }

        IloNumExpr J = cplex.sum(prods_b);

        // require integer variable to use separation oracle
        IloNumVar dummy = cplex.intVar(0, 0, "d");

        cplex.addMaximize(cplex.sum(J, dummy));
    }

    // inner class for separation oracle
    // we define the x values as
    // x_bcm[bi][ci][mi] = pi_bcm[bi][ci][mi] * sum_{ci' <= ci} (p_bc[bi][ci'])
    // for use in the shaded index sets
    // S_bmx[bi][mi](x) = { ci | x_bcm[bi][ci][mi] >= x }
    // so that we can make sure that for each bi, mi, we have
    // sum_{bi, ci in S_bmx[bi][mi](x)} (n_b[bi] * pi_bcm[bi][ci][mi] *
    // p_bc[bi][ci]) <= 1 - prod_{bi} (1 - sum_{ci in S_bmx[bi][mi](x)}
    // (p_bc[bi][ci]))^(n_b[bi])
    // the separation oracle adds any broken constraints to the problem
    private class SeparationOracle extends IloCplex.LazyConstraintCallback {

        // margin of error for separation oracle
        private static final double EPSILON = 1e-5;

        // inner class to sort pi values in ascending order
        private class PiNode implements Comparable<PiNode> {

            public double pi;
            public int ci;

            public PiNode(double pi, int ci) {

                this.pi = pi;
                this.ci = ci;
            }

            public int compareTo(PiNode that) {

                if (this.pi > that.pi)
                    return 1;
                if (this.pi < that.pi)
                    return -1;
                return 0;
            }
        }

        // inner class to sort x values in descending order
        private class XNode implements Comparable<XNode> {

            public double x;
            public int bi;
            public int ci;

            public XNode(double x, int bi, int ci) {

                this.x = x;
                this.bi = bi;
                this.ci = ci;
            }

            public int compareTo(XNode that) {

                if (this.x > that.x)
                    return -1;
                if (this.x < that.x)
                    return 1;
                return 0;
            }
        }

        // executes the separation oracle, adding any broken constraint
        protected void main() throws IloException {

            // extract pi values at current node
            double[][][] pi_mbc = new double[m][b][c];

            for (int bi = 0; bi < b; bi++) {
                for (int ci = 0; ci < c; ci++) {
                    for (int mi = 0; mi < m; mi++) {
                        pi_mbc[mi][bi][ci] = getValue(pi_bcm[bi][ci][mi]);
                    }
                }
            }

            // iterate through each item, checking that the allocation for that item is
            // feasible
            for (int mi = 0; mi < m; mi++) {

                // create max-heap to sort x nodes in descending order
                PriorityQueue<XNode> xn_y = new PriorityQueue<XNode>();

                // calculate x node values
                for (int bi = 0; bi < b; bi++) {

                    // create increasing array of pi nodes
                    PiNode[] pn_c = new PiNode[c];

                    for (int ci = 0; ci < c; ci++) {
                        pn_c[ci] = new PiNode(pi_mbc[mi][bi][ci], ci);
                    }

                    Arrays.sort(pn_c);

                    // calculate x values iteratively

                    // base case
                    double pi_curr = -1.0; // the largest pi seen so far
                    double p_sum = 0.0; // sum of all p for all pi <= pi_current

                    // iterate through each pi node
                    for (int ci1 = 0; ci1 < c; ci1++) {

                        PiNode pn = pn_c[ci1];

                        // if we have a higher pi value
                        if (pn.pi > pi_curr) {

                            // update the highest value so far
                            pi_curr = pn.pi;

                            // update the sum to include all pi nodes with this value of pi
                            for (int ci2 = ci1; ci2 < c; ci2++) {

                                // exhausted all pi nodes with this pi value
                                if (pn_c[ci2].pi > pi_curr)
                                    break;

                                p_sum += p_bc[bi][pn_c[ci2].ci];
                            }
                        }

                        // calculate x value and insert into max-heap
                        xn_y.add(new XNode(pn.pi * p_sum, bi, pn.ci));
                    }
                }

                // iterate through the threshold values of x in xn_pq and check the constraint

                // base case
                ArrayList<XNode> xn_curr_y = new ArrayList<XNode>(); // all x nodes seen so far
                double x_curr = Double.POSITIVE_INFINITY; // the smallest x seen so far
                double lhs_sum = 0.0; // current value of left hand side
                double ln_rhs_prod = 0.0; // natural log of the current value of the product in the right hand side
                double[] rhs_b = new double[b]; // current value of multiplicands in the right hand side
                for (int bi = 0; bi < b; bi++) {
                    rhs_b[bi] = 1.0;
                }

                // iterate through x nodes in decreasing order
                while (!xn_y.isEmpty()) {

                    // next x node
                    XNode xn_curr = xn_y.poll();
                    xn_curr_y.add(xn_curr);
                    x_curr = xn_curr.x;

                    // update left hand side of constraint
                    lhs_sum += n_b[xn_curr.bi] * pi_mbc[mi][xn_curr.bi][xn_curr.ci] * p_bc[xn_curr.bi][xn_curr.ci];

                    // update right hand side of constraint
                    double prod_prev = rhs_b[xn_curr.bi];
                    double prod_next = prod_prev - p_bc[xn_curr.bi][xn_curr.ci];
                    rhs_b[xn_curr.bi] = prod_next;
                    ln_rhs_prod += n_b[xn_curr.bi] * (Math.log(prod_next) - Math.log(prod_prev));

                    // if there are more x nodes with same x value, don't check constraint yet!
                    if (!xn_y.isEmpty() && xn_y.peek().x == x_curr)
                        continue;

                    // if constraint is fine, keep going!
                    if (lhs_sum <= 1.0 - Math.exp(ln_rhs_prod) + EPSILON)
                        continue;

                    // found broken constraint, add it to the problem!
                    int y = xn_curr_y.size();
                    IloNumVar[] pi_y = new IloNumVar[y];
                    double[] np_y = new double[y];

                    for (int yi = 0; yi < y; yi++) {

                        XNode xn = xn_curr_y.get(yi);

                        pi_y[yi] = pi_bcm[xn.bi][xn.ci][mi];
                        np_y[yi] = n_b[xn.bi] * p_bc[xn.bi][xn.ci];
                    }

                    add(cplex.le(cplex.scalProd(pi_y, np_y), 1.0 - Math.exp(ln_rhs_prod)));

                    return;
                }
            }
        }
    }

    // adds the separation oracle
    private void addSO() throws IloException {

        SeparationOracle separationOracle = new SeparationOracle();
        cplex.use(separationOracle);
    }

    // main entry point for RoaSolver
    // parses the command line arguments and executes the solver for all trials of
    // all problem settings
    public static void main(String[] args) throws Exception {

        // command-line flags
        boolean fullTerminalFlag = false;
        boolean fullFileFlag = false;
        boolean briefTerminalFlag = false;
        boolean briefFileFlag = false;

        ArrayList<String> fileNames = new ArrayList<String>();

        // process flags
        for (String arg : args) {

            // not a flag, so it must be a file name
            if (arg.charAt(0) != '-') {

                fileNames.add(arg);
                continue;
            }

            if (arg.equals("-ft")) {

                fullTerminalFlag = true;
                continue;
            }

            if (arg.equals("-ff")) {

                fullFileFlag = true;
                continue;
            }

            if (arg.equals("-bt")) {

                briefTerminalFlag = true;
                continue;
            }

            if (arg.equals("-bf")) {

                briefFileFlag = true;
                continue;
            }

            System.err.println("Error processing input due to unrecognized flag: " + arg);
            return;
        }

        // ensure at least some input
        if (!fullTerminalFlag && !fullFileFlag && !briefTerminalFlag && !briefFileFlag) {

            briefTerminalFlag = true;
        }

        // ensure at least one input file
        if (fileNames.size() == 0) {

            System.err.println("Error: no input file(s) specified!");
            return;
        }

        // iterate through each file to read and solve, writing according to flags
        for (String fileName : fileNames) {

            // header in terminal
            System.out.println();
            System.out.println("========================================");
            System.out.println("File: " + fileName);
            System.out.println();
            System.out.flush();

            try {

                // parse file
                Scanner sc = new Scanner(new File(fileName));
                RoaSolverParser parser = new RoaSolverParser(sc);

                // start accumulating brief output
                StringBuilder briefText = new StringBuilder(parser.getBriefTextHeading());
                StringBuilder briefCSV = new StringBuilder(parser.getBriefCSVHeading());

                // iterate through each trial
                for (RoaSolverInput input : RoaSolverInput.getInputs(parser)) {

                    // execute the trial
                    RoaSolver solver = new RoaSolver(input);
                    RoaSolverOutput output = solver.getOutput();

                    // accumulte brief output
                    briefText.append(output.toBriefText());
                    briefCSV.append(output.toBriefCSV());

                    // for full terminal output
                    if (fullTerminalFlag) {

                        System.out.println(output.toFullText());
                    }

                    // for full file output
                    if (fullFileFlag) {

                        String newFileName = fileName + output.toID() + "_solution.csv";

                        FileWriter fileWriter = new FileWriter(newFileName);
                        PrintWriter out = new PrintWriter(fileWriter);

                        out.print(output.toFullCSV());
                        out.close();

                        System.out.println();
                        System.out.println("Wrote full solution to " + newFileName);
                        System.out.println();
                    }
                }

                // for brief terminal output
                if (briefTerminalFlag) {

                    System.out.println();
                    System.out.println("========================================");
                    System.out.println("Summary of file: " + fileName);
                    System.out.println();
                    System.out.println(briefText.toString());
                }

                // for brief file output
                if (briefFileFlag) {

                    String newFileName = fileName + "_solutions.csv";

                    FileWriter fileWriter = new FileWriter(newFileName);
                    PrintWriter out = new PrintWriter(fileWriter);

                    out.print(briefCSV);
                    out.close();

                    System.out.println();
                    System.out.println("Wrote brief solution to " + newFileName);
                    System.out.println();
                }

            } catch (FileNotFoundException e) {
                System.out.println(e);
            } catch (RoaSolverError e) {
                System.err.println(e.getMessage());
            }
        }
    }
}
