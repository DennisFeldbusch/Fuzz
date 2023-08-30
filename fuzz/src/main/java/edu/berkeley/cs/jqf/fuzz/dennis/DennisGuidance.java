/*
 * Copyright (c) 2017-2018 The Regents of the University of California
 * Copyright (c) 2020-2021 Rohan Padhye
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package edu.berkeley.cs.jqf.fuzz.dennis;

import java.io.Console;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;


import org.eclipse.collections.api.list.primitive.IntList;

import edu.berkeley.cs.jqf.fuzz.guidance.TimeoutException;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance.Input;
import edu.berkeley.cs.jqf.fuzz.guidance.Guidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;
import edu.berkeley.cs.jqf.fuzz.util.CoverageFactory;
import edu.berkeley.cs.jqf.fuzz.util.FastNonCollidingCoverage;
import edu.berkeley.cs.jqf.fuzz.util.ICoverage;
import edu.berkeley.cs.jqf.fuzz.util.IOUtils;
import edu.berkeley.cs.jqf.instrument.tracing.FastCoverageSnoop;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import janala.instrument.FastCoverageListener;

/**
 * A guidance that performs coverage-guided fuzzing using two coverage maps,
 * one for all inputs and one for valid inputs only.
 *
 * @author Rohan Padhye
 */
public class DennisGuidance implements Guidance {

    /** A pseudo-random number generator for generating fresh values. */
    protected Random random;

    /** The name of the test for display purposes. */
    protected final String testName;

    // ------------ ALGORITHM BOOKKEEPING ------------

    /** The max amount of time to run for, in milli-seconds */
    protected final long maxDurationMillis;

    /** The max number of trials to run */
    protected final long maxTrials;

    /** The number of trials completed. */
    protected long numTrials = 0;

    /** The number of valid inputs. */
    protected long numValid = 0;

    /** The directory where fuzzing results are produced. */
    protected final File outputDirectory;

    /** The directory where interesting inputs are saved. */
    protected File savedCorpusDirectory;

    /** The directory where saved inputs are saved. */
    protected File savedFailuresDirectory;

    /**
     * The directory where all generated inputs are logged in sub-directories (if
     * enabled).
     */
    protected File allInputsDirectory;

    /**
     * Index of currentInput in the savedInputs -- valid after seeds are processed
     * (OK if this is inaccurate).
     */
    protected int currentParentInputIdx = 0;

    /** Number of mutated inputs generated from currentInput. */
    protected int numChildrenGeneratedForCurrentParentInput = 0;

    /**
     * Number of cycles completed (i.e. how many times we've reset
     * currentParentInputIdx to 0.
     */
    protected int cyclesCompleted = 0;

    /** Number of favored inputs in the last cycle. */
    protected int numFavoredLastCycle = 0;

    /** Blind fuzzing -- if true then the queue is always empty. */
    protected boolean blind;

    /**
     * Validity fuzzing -- if true then save valid inputs that increase valid
     * coverage
     */
    protected boolean validityFuzzing;

    /**
     * Number of saved inputs.
     *
     * This is usually the same as savedInputs.size(),
     * but we do not really save inputs in TOTALLY_RANDOM mode.
     */
    protected int numSavedInputs = 0;

    /** Coverage statistics for a single run. */
    protected ICoverage runCoverage = CoverageFactory.newInstance();

    /** Cumulative coverage statistics. */
    protected ICoverage totalCoverage = CoverageFactory.newInstance();

    /** Cumulative coverage updated on generation */
    protected ICoverage generationCoverage = CoverageFactory.newInstance();

    /** just for testing purpose */
    protected ICoverage validCoverage = CoverageFactory.newInstance();

    /** The maximum number of keys covered by any single input found so far. */
    protected int maxCoverage = 0;

    /** The set of unique failures found so far. */
    protected Set<String> uniqueFailures = new HashSet<>();

    /** save crash to specific location (should be used with EXIT_ON_CRASH) **/
    protected final String EXACT_CRASH_PATH = System.getProperty("jqf.ei.EXACT_CRASH_PATH");

    // ---------- LOGGING / STATS OUTPUT ------------

    /** Whether to print log statements to stderr (debug option; manually edit). */
    protected final boolean verbose = true;

    /** A system console, which is non-null only if STDOUT is a console. */
    protected final Console console = System.console();

    /** Time since this guidance instance was created. */
    protected final Date startTime = new Date();

    /** Time at last stats refresh. */
    protected Date lastRefreshTime = startTime;

    /** Total execs at last stats refresh. */
    protected long lastNumTrials = 0;

    /** Minimum amount of time (in millis) between two stats refreshes. */
    protected final long STATS_REFRESH_TIME_PERIOD = 300;

    /** The file where log data is written. */
    protected File logFile;

    /** The file where saved plot data is written. */
    protected File statsFile;

    /** The currently executing input (for debugging purposes). */
    protected File currentInputFile;

    /** The file contianing the coverage information */
    protected File coverageFile;

    /**
     * Use libFuzzer like output instead of AFL like stats screen
     * (https://llvm.org/docs/LibFuzzer.html#output)
     **/
    protected final boolean LIBFUZZER_COMPAT_OUTPUT = Boolean.getBoolean("jqf.ei.LIBFUZZER_COMPAT_OUTPUT");

    /** Whether to hide fuzzing statistics **/
    protected final boolean QUIET_MODE = Boolean.getBoolean("jqf.ei.QUIET_MODE");

    /** Whether to store all generated inputs to disk (can get slowww!) */
    protected final boolean LOG_ALL_INPUTS = Boolean.getBoolean("jqf.ei.LOG_ALL_INPUTS");

    // ------------- TIMEOUT HANDLING ------------

    /** Timeout for an individual run. */
    protected long singleRunTimeoutMillis;

    /** Date when last run was started. */
    protected Date runStart;

    /** Number of conditional jumps since last run was started. */
    protected long branchCount;

    /** Whether to stop/exit once a crash is found. **/
    protected final boolean EXIT_ON_CRASH = Boolean.getBoolean("jqf.ei.EXIT_ON_CRASH");

    // ------------- THREAD HANDLING ------------

    /** The first thread in the application, which usually runs the test method. */
    protected Thread firstThread;

    /**
     * Whether the application has more than one thread running
     * coverage-instrumented code
     */
    protected boolean multiThreaded = false;

    // ------------- FUZZING HEURISTICS ------------

    /** Whether to save only valid inputs **/
    protected final boolean SAVE_ONLY_VALID = Boolean.getBoolean("jqf.ei.SAVE_ONLY_VALID");

    /** Max input size to generate. */
    protected final int MAX_INPUT_SIZE = Integer.getInteger("jqf.ei.MAX_INPUT_SIZE", 10240);

    /**
     * Whether to generate EOFs when we run out of bytes in the input, instead of
     * randomly generating new bytes.
     **/
    protected final boolean GENERATE_EOF_WHEN_OUT = Boolean.getBoolean("jqf.ei.GENERATE_EOF_WHEN_OUT");

    /** Baseline number of mutated children to produce from a given parent input. */
    protected final int NUM_CHILDREN_BASELINE = 50;

    /**
     * Multiplication factor for number of children to produce for favored inputs.
     */
    protected final int NUM_CHILDREN_MULTIPLIER_FAVORED = 20;

    /** Mean number of mutations to perform in each round. */
    protected final double MEAN_MUTATION_COUNT = 8.0;

    /** Mean number of contiguous bytes to mutate in each mutation. */
    protected final double MEAN_MUTATION_SIZE = 4.0; // Bytes

    /**
     * Whether to save inputs that only add new coverage bits (but no new
     * responsibilities).
     */
    protected final boolean DISABLE_SAVE_NEW_COUNTS = Boolean.getBoolean("jqf.ei.DISABLE_SAVE_NEW_COUNTS");

    /**
     * Whether to steal responsibility from old inputs (this increases computation
     * cost).
     */
    protected final boolean STEAL_RESPONSIBILITY = Boolean.getBoolean("jqf.ei.STEAL_RESPONSIBILITY");

    protected final int POPULATION_SIZE = Integer.getInteger("jqf.ei.POPULATION_SIZE", 1000);

    protected final int INITIAL_VALUE_SIZE = Integer.getInteger("jqf.ei.INITIAL_VALUE_SIZE", 30);

    protected Integer genCounter = 0;

    protected Coverage coverage = new Coverage();

    protected ArrayList<LinearInput> population = new ArrayList<>();

    protected LinearInput candidate;

    protected int counter;

    /**
     * Creates a new Zest guidance instance with optional duration,
     * optional trial limit, and possibly deterministic PRNG.
     *
     * @param testName           the name of test to display on the status screen
     * @param duration           the amount of time to run fuzzing for, where
     *                           {@code null} indicates unlimited time.
     * @param trials             the number of trials for which to run fuzzing,
     *                           where
     *                           {@code null} indicates unlimited trials.
     * @param outputDirectory    the directory where fuzzing results will be written
     * @param sourceOfRandomness a pseudo-random number generator
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, Long trials, File outputDirectory,
            Random sourceOfRandomness) throws IOException {
        this.random = sourceOfRandomness;
        this.testName = testName;
        this.maxDurationMillis = duration != null ? duration.toMillis() : Long.MAX_VALUE;
        this.maxTrials = trials != null ? trials : Long.MAX_VALUE;
        this.outputDirectory = outputDirectory;
        this.blind = Boolean.getBoolean("jqf.ei.TOTALLY_RANDOM");
        this.validityFuzzing = !Boolean.getBoolean("jqf.ei.DISABLE_VALIDITY_FUZZING");
        prepareOutputDirectory();

        if (this.runCoverage instanceof FastCoverageListener) {
            FastCoverageSnoop.setFastCoverageListener((FastCoverageListener) this.runCoverage);
        }

        // Try to parse the single-run timeout
        String timeout = System.getProperty("jqf.ei.TIMEOUT");
        if (timeout != null && !timeout.isEmpty()) {
            try {
                // Interpret the timeout as milliseconds (just like `afl-fuzz -t`)
                this.singleRunTimeoutMillis = Long.parseLong(timeout);
            } catch (NumberFormatException e1) {
                throw new IllegalArgumentException("Invalid timeout duration: " + timeout);
            }
        }
    }

    /**
     * Creates a new Zest guidance instance with seed input files and optional
     * duration, optional trial limit, an possibly deterministic PRNG.
     *
     * @param testName           the name of test to display on the status screen
     * @param duration           the amount of time to run fuzzing for, where
     *                           {@code null} indicates unlimited time.
     * @param trials             the number of trials for which to run fuzzing,
     *                           where
     *                           {@code null} indicates unlimited trials.
     * @param outputDirectory    the directory where fuzzing results will be written
     * @param seedInputFiles     one or more input files to be used as initial
     *                           inputs
     * @param sourceOfRandomness a pseudo-random number generator
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, Long trials, File outputDirectory, File[] seedInputFiles,
            Random sourceOfRandomness) throws IOException {
        this(testName, duration, trials, outputDirectory, sourceOfRandomness);
        if (seedInputFiles != null) {
            for (File seedInputFile : seedInputFiles) {
                // seedInputs.add(new SeedInput(seedInputFile));
            }
        }
    }

    /**
     * Creates a new Zest guidance instance with seed input directory and optional
     * duration, optional trial limit, an possibly deterministic PRNG.
     *
     * @param testName           the name of test to display on the status screen
     * @param duration           the amount of time to run fuzzing for, where
     *                           {@code null} indicates unlimited time.
     * @param trials             the number of trials for which to run fuzzing,
     *                           where
     *                           {@code null} indicates unlimited trials.
     * @param outputDirectory    the directory where fuzzing results will be written
     * @param seedInputDir       the directory containing one or more input files to
     *                           be used as initial inputs
     * @param sourceOfRandomness a pseudo-random number generator
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, Long trials, File outputDirectory, File seedInputDir,
            Random sourceOfRandomness) throws IOException {
        this(testName, duration, trials, outputDirectory, IOUtils.resolveInputFileOrDirectory(seedInputDir),
                sourceOfRandomness);
    }

    /**
     * Creates a new Zest guidance instance with seed inputs and
     * optional duration.
     *
     * @param testName        the name of test to display on the status screen
     * @param duration        the amount of time to run fuzzing for, where
     *                        {@code null} indicates unlimited time.
     * @param outputDirectory the directory where fuzzing results will be written
     * @param seedInputDir    the directory containing one or more input files to be
     *                        used as initial inputs
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, File outputDirectory, File seedInputDir)
            throws IOException {
        this(testName, duration, null, outputDirectory, seedInputDir, new Random());
    }

    /**
     * Creates a new Zest guidance instance with seed inputs and
     * optional duration.
     *
     * @param testName        the name of test to display on the status screen
     * @param duration        the amount of time to run fuzzing for, where
     *                        {@code null} indicates unlimited time.
     * @param outputDirectory the directory where fuzzing results will be written
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, File outputDirectory) throws IOException {
        this(testName, duration, null, outputDirectory, new Random());
    }

    /**
     * Creates a new Zest guidance instance with seed inputs and
     * optional duration.
     *
     * @param testName        the name of test to display on the status screen
     * @param duration        the amount of time to run fuzzing for, where
     *                        {@code null} indicates unlimited time.
     * @param outputDirectory the directory where fuzzing results will be written
     * @throws IOException if the output directory could not be prepared
     */
    public DennisGuidance(String testName, Duration duration, File outputDirectory, File[] seedFiles)
            throws IOException {
        this(testName, duration, null, outputDirectory, seedFiles, new Random());
    }

    private void prepareOutputDirectory() throws IOException {
        // Create the output directory if it does not exist
        IOUtils.createDirectory(outputDirectory);

        // Name files and directories after AFL
        this.savedCorpusDirectory = IOUtils.createDirectory(outputDirectory, "corpus");
        this.savedFailuresDirectory = IOUtils.createDirectory(outputDirectory, "failures");
        if (LOG_ALL_INPUTS) {
            this.allInputsDirectory = IOUtils.createDirectory(outputDirectory, "all");
            IOUtils.createDirectory(allInputsDirectory, "success");
            IOUtils.createDirectory(allInputsDirectory, "invalid");
            IOUtils.createDirectory(allInputsDirectory, "failure");
        }
        this.statsFile = new File(outputDirectory, "plot_data");
        this.logFile = new File(outputDirectory, "fuzz.log");
        this.currentInputFile = new File(outputDirectory, ".cur_input");
        this.coverageFile = new File(outputDirectory, "coverage_hash");

        // Delete everything that we may have created in a previous run.
        // Trying to stay away from recursive delete of parent output directory in case
        // there was a
        // typo and that was not a directory we wanted to nuke.
        // We also do not check if the deletes are actually successful.
        statsFile.delete();
        logFile.delete();
        coverageFile.delete();
        for (File file : savedCorpusDirectory.listFiles()) {
            file.delete();
        }
        for (File file : savedFailuresDirectory.listFiles()) {
            file.delete();
        }

        appendLineToFile(statsFile, getStatNames());
    }

    protected String getStatNames() {
        return "elapsed_time\tbranches_covered";
        /* 
        return "# unix_time, cycles_done, cur_path, paths_total, pending_total, " +
                "pending_favs, map_size, unique_crashes, unique_hangs, max_depth, execs_per_sec, valid_inputs, invalid_inputs, valid_cov, all_covered_probes, valid_covered_probes";
                */
    }

    /* Writes a line of text to a given log file. */
    protected void appendLineToFile(File file, String line) throws GuidanceException {
        try (PrintWriter out = new PrintWriter(new FileWriter(file, true))) {
            out.println(line);
        } catch (IOException e) {
            throw new GuidanceException(e);
        }

    }

    /* Writes a line of text to the log file. */
    protected void infoLog(String str, Object... args) {
        if (verbose) {
            String line = String.format(str, args);
            if (logFile != null) {
                appendLineToFile(logFile, line);

            } else {
                System.err.println(line);
            }
        }
    }

    protected String millisToDuration(long millis) {
        long seconds = TimeUnit.MILLISECONDS.toSeconds(millis % TimeUnit.MINUTES.toMillis(1));
        long minutes = TimeUnit.MILLISECONDS.toMinutes(millis % TimeUnit.HOURS.toMillis(1));
        long hours = TimeUnit.MILLISECONDS.toHours(millis);
        String result = "";
        if (hours > 0) {
            result = hours + "h ";
        }
        if (hours > 0 || minutes > 0) {
            result += minutes + "m ";
        }
        result += seconds + "";
        //result += seconds + "s";
        return result;
    }

    // Call only if console exists
    protected void displayStats(boolean force) {
        Date now = new Date();
        long intervalMilliseconds = now.getTime() - lastRefreshTime.getTime();
        intervalMilliseconds = Math.max(1, intervalMilliseconds);
        if (intervalMilliseconds < STATS_REFRESH_TIME_PERIOD && !force) {
            return;
        }
        long interlvalTrials = numTrials - lastNumTrials;
        long intervalExecsPerSec = interlvalTrials * 1000L;
        double intervalExecsPerSecDouble = interlvalTrials * 1000.0;
        if (intervalMilliseconds != 0) {
            intervalExecsPerSec = interlvalTrials * 1000L / intervalMilliseconds;
            intervalExecsPerSecDouble = interlvalTrials * 1000.0 / intervalMilliseconds;
        }
        lastRefreshTime = now;
        lastNumTrials = numTrials;
        long elapsedMilliseconds = now.getTime() - startTime.getTime();
        elapsedMilliseconds = Math.max(1, elapsedMilliseconds);
        long execsPerSec = numTrials * 1000L / elapsedMilliseconds;

        int nonZeroCount = totalCoverage.getNonZeroCount();
        double nonZeroFraction = nonZeroCount * 100.0 / totalCoverage.size();
        int nonZeroValidCount = validCoverage.getNonZeroCount();
        double nonZeroValidFraction = nonZeroValidCount * 100.0 / validCoverage.size();

        if (console != null) {
            if (LIBFUZZER_COMPAT_OUTPUT) {
                console.printf("#%,d\tNEW\tcov: %,d exec/s: %,d L: %,d\n", numTrials, nonZeroValidCount,
                        intervalExecsPerSec, 5);
            } else if (!QUIET_MODE) {
                console.printf("\033[2J");
                console.printf("\033[H");
                console.printf(this.getTitle() + "\n");
                if (this.testName != null) {
                    console.printf("Test name:            %s\n", this.testName);
                }

                String instrumentationType = "Janala";
                if (this.runCoverage instanceof FastNonCollidingCoverage) {
                    instrumentationType = "Fast";
                }
                console.printf("Instrumentation:      %s\n", instrumentationType);
                console.printf("Results directory:    %s\n", this.outputDirectory.getAbsolutePath());
                console.printf("Elapsed time:         %s (%s)\n", millisToDuration(elapsedMilliseconds),
                        maxDurationMillis == Long.MAX_VALUE ? "no time limit"
                                : ("max " + millisToDuration(maxDurationMillis)));
                console.printf("Number of executions: %,d (%s)\n", numTrials,
                        maxTrials == Long.MAX_VALUE ? "no trial limit" : ("max " + maxTrials));
                console.printf("Valid inputs:         %,d (%.2f%%)\n", numValid, numValid * 100.0 / numTrials);
                console.printf("Cycles completed:     %d\n", cyclesCompleted);
                console.printf("Unique failures:      %,d\n", uniqueFailures.size());
                console.printf("Queue size:           %,d (%,d favored last cycle)\n", 5, numFavoredLastCycle);
                console.printf("Current parent input: %s\n", "currentParentInputDesc");
                console.printf("Execution speed:      %,d/sec now | %,d/sec overall\n", intervalExecsPerSec,
                        execsPerSec);
                console.printf("Total coverage:       %,d branches (%.2f%% of map)\n", nonZeroCount, nonZeroFraction);
                console.printf("Valid coverage:       %,d branches (%.2f%% of map)\n", this.branchCount,
                        nonZeroValidFraction);
                console.printf("Total size:           %,d branches\n", totalCoverage.size());
                console.printf("Generation:           %,d \n", this.counter);
                console.printf("Generation coverage:  %,d\n", generationCoverage.getNonZeroCount());
            }
        }

        String plotData = String.format("%s\t%d", millisToDuration(elapsedMilliseconds), nonZeroCount);
        /* 
        String plotData = String.format("%d, %d, %d, %d, %d, %d, %.2f%%, %d, %d, %d, %.2f, %d, %d, %.2f%%, %d, %d",
                TimeUnit.MILLISECONDS.toSeconds(now.getTime()), cyclesCompleted, currentParentInputIdx,
                numSavedInputs, 0, 0, nonZeroFraction, uniqueFailures.size(), 0, 0, intervalExecsPerSecDouble,
                numValid, numTrials - numValid, nonZeroValidFraction, nonZeroCount, nonZeroValidCount);
                */
        appendLineToFile(statsFile, plotData);
    }

    /** Updates the data in the coverage file */
    protected void updateCoverageFile() {
        try {
            PrintWriter pw = new PrintWriter(coverageFile);
            pw.close();
        } catch (FileNotFoundException ignore) {
            throw new GuidanceException(ignore);
        }
    }

    /* Returns the banner to be displayed on the status screen */
    protected String getTitle() {
        if (blind) {
            return "Genetic Algorithm Fuzzing\n" +
                    "--------------------------------------------\n";
        } else {
            return "Fuzzing with Dennis\n" +
                    "--------------------------\n";
        }
    }

    public void setBlind(boolean blind) {
        this.blind = blind;
    }

    /**
     * called once to initialize a random population
     * 
     * 
     */
    protected void initializePopulation() {
        console.printf("Initializing population\n");
        for (int i = 0; i < POPULATION_SIZE; i++) {
            this.population.add(new LinearInput((int) (Math.random() * INITIAL_VALUE_SIZE)));
        }
    }

    /**
     * 
     * 
     * @param mutationRate
     */
    protected void mutate(double mutationRate) {
        int numberOfMutations = (int) Math.round(mutationRate * this.population.size());
        for (int i = 0; i < numberOfMutations; i++) {
            int index = (int) (Math.random() * this.population.size());
            this.population.get(index).mutate();
        }

    }

    /**
     * Take two random candidates from the population
     * generate two randowm crossover points
     * swap the genes between the two points
     * 
     * @param crossoverRate
     */
    protected void crossover(double crossoverRate) {
        int numberOfCrossovers = (int) Math.round(crossoverRate * this.population.size());
        for (int i = 0; i < numberOfCrossovers; i++) {
            int firstIndex = (int) (Math.random() * this.population.size());
            int secondIndex = (int) (Math.random() * this.population.size());
            while (firstIndex == secondIndex) {
                secondIndex = (int) (Math.random() * this.population.size());
            }
            LinearInput firstCandidate = this.population.get(firstIndex).copy();
            LinearInput secondCandidate = this.population.get(secondIndex).copy();
            int firstCrossoverPoint = (int) (Math.random() * firstCandidate.size());
            int secondCrossoverPoint = (int) (Math.random() * secondCandidate.size());
            LinearInput newFirstCandidate = new LinearInput();
            newFirstCandidate.setFitness(firstCandidate.getFitness());
            LinearInput newSecondCandidate = new LinearInput();
            newSecondCandidate.setFitness(secondCandidate.getFitness());

            for (int j = 0; j < firstCrossoverPoint; j++) {
                newFirstCandidate.values.add(firstCandidate.values.get(j));
            }
            for (int j = 0; j < secondCrossoverPoint; j++) {
                newSecondCandidate.values.add(secondCandidate.values.get(j));
            }
            for (int j = secondCrossoverPoint; j < secondCandidate.size(); j++) {
                newFirstCandidate.values.add(secondCandidate.values.get(j));
            }
            for (int j = firstCrossoverPoint; j < firstCandidate.size(); j++) {
                newSecondCandidate.values.add(firstCandidate.values.get(j));
            }

            this.population.set(secondIndex, newSecondCandidate);
            this.population.set(firstIndex, newFirstCandidate);

        }
    }

    /**
     * 
     */
    protected void fitnessProportionalSelection() {

        // create a deep copy of the population
        ArrayList<LinearInput> populationCopy = new ArrayList<>();
        for (LinearInput entry : this.population) {
            //System.out.println("fitness from outside: " + entry.getFitness());
            populationCopy.add(entry.copy());
        }

        int totalFitness = 0;

        for (LinearInput entry : populationCopy) {
            //System.out.println("fitness from inside: " + entry.getFitness());
            totalFitness += entry.getFitness();
            entry.setFitness(totalFitness);
        }

        //System.out.println("total fitness: " + totalFitness);

        // select a random entry with respect to the corresponding fitness compared to
        // the total fitness
        for (int i = 0; i < POPULATION_SIZE; i++) {
            int randomFitness = (int) (Math.random() * totalFitness);
            for (LinearInput entry : populationCopy) {
                if (randomFitness <= entry.getFitness()) {
                    this.population.set(i, entry);
                    break;
                }
            }
        }
    }

    protected void rankBasedSelection() {
        // create a deep copy of the population
        ArrayList<LinearInput> populationCopy = new ArrayList<>();
        for (LinearInput entry : this.population) {
            populationCopy.add(entry.copy());
        }

        // sort the population by fitness
        Collections.sort(populationCopy, new Comparator<LinearInput>() {
            @Override
            public int compare(LinearInput o1, LinearInput o2) {
                return o1.getFitness() - o2.getFitness();
            }
        });

        int totalFitness = 0; 

        for (int i = 0; i < POPULATION_SIZE; i++) {
            totalFitness += i;
            populationCopy.get(i).setFitness(totalFitness);
        }

        // select a random entry with respect to the corresponding fitness compared to
        // the total fitness
        for (int i = 0; i < POPULATION_SIZE; i++) {
            int randomFitness = (int) (Math.random() * totalFitness);
            for (LinearInput entry : populationCopy) {
                if (randomFitness <= entry.getFitness()) {
                    this.population.set(i, entry);
                    break;
                }
            }
        }

    }



    /**
     * creates a new population based on the previously
     * calculated fitness for each candidate
     *
     * 1. Mutation
     * 2. Crossover
     * 3. FitnessProportionalSelection
     * 4. update totalCoverage
     *
     */
    protected void createNewPopulation() {
        //System.out.println("");

        // should be called only once
        if (this.population.isEmpty()) {
            initializePopulation();
            this.candidate = getCandidateFromPopulation();
            return;
        }

        // works
        this.generationCoverage = totalCoverage.copy();

        rankBasedSelection();
        //fitnessProportionalSelection();
        mutate(0.2);
        crossover(0.2);

        // reset fitness
        for (LinearInput entry : this.population) {
            entry.setFitness(-1);
        }

        // mutation
        // crossover
        // fitnessProportionalSelection

        this.candidate = getCandidateFromPopulation();

    }

    /**
     * calculates the fitness for the currenct candidate
     * updates fitness of candidate in population list
     *
     */
    protected void calculateFitness() {

        this.numTrials++;

        IntList newCoverage = runCoverage.computeNewCoverage(generationCoverage);
        int fitness = newCoverage.size();

        this.population.get(this.genCounter).setFitness(fitness);
    }

    /**
     *
     * returns a candidate from the population list
     * where the fitness is not set
     *
     * @return String
     *
     */
    protected LinearInput getCandidateFromPopulation() {

        if (this.population.size() == 0) {
            return null;
        }

        if (genCounter == POPULATION_SIZE) {
            this.genCounter = 0;
            this.counter++;
            return null;    
        }

        return this.population.get(genCounter);
    }

    /**
     * Returns an InputStream that delivers parameters to the generators.
     *
     * Note: The variable `currentInput` has been set to point to the input
     * to mutate.
     *
     * @return an InputStream that delivers parameters to the generators
     */
    protected InputStream createParameterStream() {
        // Return an input stream that reads bytes from a linear array
        return new InputStream() {
            int bytesRead = 0;

            @Override
            public int read() throws IOException {
                assert candidate instanceof LinearInput : "DennisGuidance should only mutate LinearInput(s)";

                // For linear inputs, get with key = bytesRead (which is then incremented)
                LinearInput linearInput = (LinearInput) candidate;
                // Attempt to get a value from the list, or else generate a random value
                int ret = linearInput.getOrGenerateFresh(bytesRead++, random);
                // infoLog("read(%d) = %d", bytesRead, ret);
                return ret;
            }
        };
    }

    @Override
    public InputStream getInput() throws GuidanceException {
        conditionallySynchronize(multiThreaded, () -> {
            totalCoverage.updateBits(runCoverage);
            this.runCoverage.clear();
            this.candidate = getCandidateFromPopulation();

            if (this.candidate == null) {
                createNewPopulation();
            }

        });
        return createParameterStream();

    }

    @Override
    public boolean hasInput() {
        Date now = new Date();
        long elapsedMilliseconds = now.getTime() - startTime.getTime();
        if (EXIT_ON_CRASH && uniqueFailures.size() >= 1) {
            // exit
            return false;
        }
        if (elapsedMilliseconds < maxDurationMillis
                && numTrials < maxTrials) {
            return true;
        } else {
            displayStats(true);
            return false;
        }
    }

    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {
        conditionallySynchronize(multiThreaded, () -> {

            this.runStart = null;
            boolean valid = result == Result.SUCCESS;
            calculateFitness();
            this.genCounter++;

            if (valid) {
                // Increment valid counter
                numValid++;
            }

            //this.numTrials++;
            displayStats(false);
        });

    }

    @Override
    public Consumer<TraceEvent> generateCallBack(Thread thread) {
        if (firstThread == null) {
            firstThread = thread;
        } else if (firstThread != thread) {
            multiThreaded = true;
        }
        return this::handleEvent;
    }

    /**
     * Handles a trace event generated during test execution.
     *
     * Not used by FastNonCollidingCoverage, which does not allocate an
     * instance of TraceEvent at each branch probe execution.
     *
     * @param e the trace event to be handled
     */
    protected void handleEvent(TraceEvent e) {
        conditionallySynchronize(multiThreaded, () -> {
            // Collect totalCoverage
            ((Coverage) runCoverage).handleEvent(e);
            // Check for possible timeouts every so often
            if (this.singleRunTimeoutMillis > 0 &&
                    this.runStart != null && (++this.branchCount) % 10_000 == 0) {
                long elapsed = new Date().getTime() - runStart.getTime();
                if (elapsed > this.singleRunTimeoutMillis) {
                    throw new TimeoutException(elapsed, this.singleRunTimeoutMillis);
                }
            }
        });
    }

    protected void conditionallySynchronize(boolean cond, Runnable task) {
        if (cond) {
            synchronized (this) {
                task.run();
            }
        } else {
            task.run();
        }
    }

    public class LinearInput extends Input<Integer> {

        /** A list of byte values (0-255) ordered by their index. */
        protected ArrayList<Integer> values;

        /** Stores the fitness */
        protected Integer fitness = -1;

        /** The number of bytes requested so far */
        protected int requested = 0;

        public LinearInput() {
            super();
            this.values = new ArrayList<>();
            this.fitness = -1;
        }

        public LinearInput(int random) {
            super();
            this.values = new ArrayList<>();
            // fill arraylist with random values in random size
            for (int i = 0; i < random; i++) {
                int randomValue = (int) (Math.random() * 256);
                this.values.add(randomValue);
            }
            this.fitness = -1;

        }

        public LinearInput(LinearInput other) {
            super(other);
            this.values = new ArrayList<>(other.values);
            this.fitness = other.getFitness();
        }

        public LinearInput copy() {
            return new LinearInput(this);
        }

        /** get values */
        public ArrayList<Integer> getValues() {
            return this.values;
        }

        /** set fitness */
        public void setFitness(Integer fitness) {
            this.fitness = fitness;
        }

        public Integer getFitness() {
            return this.fitness;
        }

        public void mutate() {
            // mutating
            int choice = (int) (Math.random() * 3);
            int index = (int) (Math.random() * this.values.size());
            Integer gene = (int) (Math.random() * 256);
            if (choice == 0) {
                // add
                this.values.add(index, gene);
            } else {
                // replace
                this.values.set(index, gene);
            }
        }

        @Override
        public int getOrGenerateFresh(Integer key, Random random) {
            // Otherwise, make sure we are requesting just beyond the end-of-list
            // assert (key == values.size());
            /*
             * if (key != requested) {
             * throw new
             * IllegalStateException(String.format("Bytes from linear input out of order. "
             * +
             * "Size = %d, Key = %d", this.values.size(), key));
             * }
             */

            // Don't generate over the limit
            if (requested >= MAX_INPUT_SIZE) {
                return -1;
            }

            // If it exists in the list, return it
            if (key < this.values.size()) {
                requested++;
                // infoLog("Returning old byte at key=%d, total requested=%d", key, requested);
                // System.out.println("Value: " + values.get(key));
                return this.values.get(key);
            }

            // Handle end of stream
            if (GENERATE_EOF_WHEN_OUT) {
                return -1;
            } else {
                // Just generate a random input
                int val = random.nextInt(256);
                this.values.add(val);
                requested++;
                return val;
            }
        }

        @Override
        public String toString() {
            String ret = "";
            for (int i = 0; i < this.values.size(); i++) {
                ret += this.values.get(i) + " ";
            }

            return ret;
        }

        @Override
        public int size() {
            return this.values.size();
        }

        /**
         * Truncates the input list to remove values that were never actually requested.
         *
         * <p>
         * Although this operation mutates the underlying object, the effect should
         * not be externally visible (at least as long as the test executions are
         * deterministic).
         * </p>
         */
        @Override
        public void gc() {
            // Remove elements beyond "requested"
            values = new ArrayList<>(values.subList(0, requested));
            values.trimToSize();

            // Inputs should not be empty, otherwise mutations don't work
            if (values.isEmpty()) {
                throw new IllegalArgumentException(
                        "Input is either empty or nothing was requested from the input generator.");
            }
        }

        @Override
        public Input fuzz(Random random) {
            // Clone this input to create initial version of new child
            LinearInput newInput = new LinearInput(this);

            // Stack a bunch of mutations
            int numMutations = sampleGeometric(random, MEAN_MUTATION_COUNT);
            // newInput.desc += ",havoc:"+numMutations;

            boolean setToZero = random.nextDouble() < 0.1; // one out of 10 times

            for (int mutation = 1; mutation <= numMutations; mutation++) {

                // Select a random offset and size
                int offset = random.nextInt(newInput.values.size());
                int mutationSize = sampleGeometric(random, MEAN_MUTATION_SIZE);

                // desc += String.format(":%d@%d", mutationSize, idx);

                // Mutate a contiguous set of bytes from offset
                for (int i = offset; i < offset + mutationSize; i++) {
                    // Don't go past end of list
                    if (i >= newInput.values.size()) {
                        break;
                    }

                    // Otherwise, apply a random mutation
                    int mutatedValue = setToZero ? 0 : random.nextInt(256);
                    newInput.values.set(i, mutatedValue);
                }
            }

            return newInput;
        }

        @Override
        public Iterator<Integer> iterator() {
            return values.iterator();
        }
    }

}
