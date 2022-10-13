package com.company;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class Main {
    public static class Task implements Callable<Long> {
        private int counterCommand;
        private int totalCommands;
        private A4Reporter rep;
        private CompModule world;
        private Command cmd;
        private A4Options opt;

        public Task(
            int counterCommand,
            int totalCommands,
            A4Reporter rep,
            CompModule world,
            Command cmd, A4Options opt)
        {
            this.counterCommand = counterCommand;
            this.totalCommands = totalCommands;
            this.rep = rep;
            this.world = world;
            this.cmd = cmd;
            this.opt = opt;
        }

        @Override
        public Long call() throws Exception {
            System.out.println(cmd);
            System.out.println("Running " + counterCommand + " out of " + totalCommands);

            long startTime = System.nanoTime();
            A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, opt);
            long endTime = System.nanoTime();
            long duration = (endTime - startTime) / 1000000;

            System.out.println("Duration Time: " + duration);
            System.out.println("Command: " + cmd.label + " Some counter-example ------ " + sol.satisfiable());

            return duration;
        }
    }

    public static Map<String, SortedSet<ScopeTracker>> timedoutScope = new HashMap<>();

    public static class ScopeTracker implements Comparable<ScopeTracker> {
        private int steps;
        private int value;
        private int ballot;
        private int quorum;
        private String solver;
        private String strategy;

        public ScopeTracker(int steps, int value, int ballot, int quorum, String solver, String strategy) {
            this.steps = steps;
            this.value = value;
            this.ballot = ballot;
            this.quorum = quorum;
            this.solver = solver;
            this.strategy = strategy;
        }

        @Override
        public int compareTo(ScopeTracker o) {
            int compare = ballot - o.ballot;
            if (compare == 0) {
                compare = quorum - o.quorum;
                if (compare == 0) {
                    compare = value - o.value;
                    if (compare == 0) {
                        compare = steps - o.steps;
                    }
                }
            }
            return compare;
        }

        public int otherCompareTo(ScopeTracker o) {
            int compare = ballot - o.ballot;
            if (compare == 0) {
                compare = quorum - o.quorum;
                if (compare == 0) {
                    compare = value - o.value;
                }
            }
            return compare;
        }
    }

    public static void main(String[] args) throws Exception {
        String basePath = System.getProperty("user.dir") + "/";

        String fixedSolver = null;
        String fixedProtocol = null;
        String fixedMessageType = null;
        if (args.length > 0) {
            basePath = args[0];
            if (args.length > 1) {
                fixedSolver = args[1];
            }
            if (args.length > 2) {
                fixedProtocol = args[2];
                fixedMessageType = args[3];
            }
        }

        System.out.println("Base path: " + basePath);

        ArrayList<String> protocols = new ArrayList<>();
        if (fixedProtocol == null) {
            protocols.add("Paxos");
            protocols.add("VerticalPaxos");
        } else {
            protocols.add(fixedProtocol);
        }

        HashMap<String, List<String>> messageTypes = new HashMap<>();
        if (fixedMessageType == null) {
            messageTypes.put("Paxos", Arrays.asList(
                "scope-paxos-dynamic-message",
                "scope-paxos-static-message",
                "scope-paxos-no-message")
            );
            messageTypes.put("VerticalPaxos", Arrays.asList(
                "scope-vertical-paxosI-dynamic-message",
                "scope-vertical-paxosII-dynamic-message",
                "scope-vertical-paxosI-static-message",
                "scope-vertical-paxosII-static-message",
                "scope-vertical-paxosI-no-message",
                "scope-vertical-paxosII-no-message")
            );
        } else {
            messageTypes.put(fixedProtocol, Arrays.asList(
                fixedMessageType)
            );
        }

        HashMap<String, A4Options.SatSolver> solvers = new HashMap();
        solvers.put("GlucoseJNI", A4Options.SatSolver.GlucoseJNI);
        solvers.put("Glucose41JNI", A4Options.SatSolver.Glucose41JNI);
        solvers.put("LingelingJNI", A4Options.SatSolver.LingelingJNI);
        solvers.put("PLingelingJNI", A4Options.SatSolver.PLingelingJNI);
        solvers.put("MiniSatJNI", A4Options.SatSolver.MiniSatJNI);
        solvers.put("ElectrodX", A4Options.SatSolver.ElectrodX);

        HashSet<String> solversToUse = new HashSet();
        if (fixedSolver == null) {
            solversToUse.add("GlucoseJNI");
            solversToUse.add("Glucose41JNI");
            solversToUse.add("LingelingJNI");
            solversToUse.add("MiniSatJNI");
        } else {
            solversToUse.add(fixedSolver);
        }

        HashMap<String, Integer> decomposeStrategies = new HashMap<>();
        decomposeStrategies.put("Batch", 0);
        decomposeStrategies.put("Hybrid", 1);
        decomposeStrategies.put("Parallel", 2);

        HashMap<String, List<String>> strategies = new HashMap();
        strategies.put("GlucoseJNI", Arrays.asList("Batch", "Hybrid", "Parallel"));
        strategies.put("LingelingJNI", Arrays.asList("Batch"));
        strategies.put("PLingelingJNI", Arrays.asList("Batch"));
        strategies.put("ElectrodX", Arrays.asList("Batch"));
        strategies.put("Glucose41JNI", Arrays.asList("Batch", "Hybrid", "Parallel"));
        strategies.put("MiniSatJNI", Arrays.asList("Batch", "Hybrid", "Parallel"));

        for (String protocol : protocols) {
            final String modelPrefix = basePath + protocol + "/" ;
            final String outputFilenamePrefix = basePath + "Plots/" + protocol + "/";

            for (int run = 1; run <= 1; run++) {
                for (String messageType : messageTypes.get(protocol)) {
                    String model = modelPrefix + messageType + ".als";
                    for (String solver : solversToUse) {
                        for (String strategyName : strategies.get(solver)) {
                            Integer strategy = decomposeStrategies.get(strategyName);

                            String outputFilename = outputFilenamePrefix + messageType + "-" + solver + "-" + strategyName + "-" + run + ".txt";
                            FileWriter myFile = new FileWriter(outputFilename);
                            PrintWriter printWriter = new PrintWriter(myFile);

                            FileReader myFileReader = new FileReader(model);
                            BufferedReader readReader = new BufferedReader(myFileReader);

                            String line = readReader.readLine();

                            readReader.close();
                            myFileReader.close();

                            String[] splits = line.split(":");
                            String[] acceptors = splits[2].split("-");

                            printWriter.print("Min acceptors:" + acceptors[0].trim());
                            printWriter.print("\nMax acceptors:" + acceptors[1].trim());
                            try {
                                A4Reporter rep = new A4Reporter();
                                File tmpAls = CompUtil.flushModelToFile(model, null);

                                CompModule world = CompUtil.parseEverything_fromFile(rep, null, model);
                                A4Options opt = new A4Options();
                                opt.solver = solvers.get(solver);
                                opt.originalFilename = tmpAls.getAbsolutePath();
                                opt.decompose_mode = strategy; //This option specifies the decompose strategy (0=Off 1=Hybrid 2=Parallel)
                                opt.decompose_threads = 16;

                                final int totalCommands = world.getAllCommands().size();
                                System.out.println("Running " + run + " --> " + totalCommands + " commands with solver " + solver + " message type " + messageType + " strategy " + strategyName);
                                int counterCommand = 0;
                                for (Command cmd : world.getAllCommands()) {
                                    counterCommand++;
                                    String duration = "Timeout";
                                    if (checkTracked(messageType, solver, strategyName, cmd)) {
                                        Task task = new Task(counterCommand, totalCommands, rep, world, cmd, opt);
                                        ExecutorService executor = Executors.newSingleThreadExecutor();
                                        Future<Long> result = executor.submit(task);
                                        try {
                                            duration = Long.toString(result.get(10, TimeUnit.MINUTES));
                                        } catch (ExecutionException ex) {
                                            duration = "Error";
                                            System.out.println("Duration Time: " + duration);
                                            System.out.println("Command: " + cmd.label + " Some counter-example ------ Error");
                                            System.out.println(ex);
                                        } catch (TimeoutException ex) {
                                            System.out.println("Exception: " + ex);
                                            System.out.println("Duration Time: " + duration);
                                            System.out.println("Command: " + cmd.label + " Some counter-example ------ Timeout");
                                        }
                                        executor.shutdownNow();
                                    } else {
                                        System.out.println(cmd);
                                        System.out.println("Skipping " + counterCommand + " out of " + totalCommands);
                                        System.out.println("Duration Time: " + duration);
                                        System.out.println("Command: " + cmd.label + " Some counter-example ------ Timeout");
                                    }

                                    if (protocol.equals("Paxos")) {
                                        if (messageType.equals("scope-paxos-no-message")) { //because there is no message
                                            /*
                                             Scope: exactly 2 Value, 2 Quorum, exactly 3 Acceptor, exactly 2 Ballot, exactly 4 Vote
                                             Label: ChosenValue
                                            */
                                            printWriter.print("\nScope: " + cmd + '\n' + "Label: " + cmd.label + ", Value: " + cmd.scope.get(0)
                                                + ", Quorum: " + cmd.scope.get(1) + ", Acceptors: " + cmd.scope.get(2) + ", Ballot: "
                                                + cmd.scope.get(3) + ", Vote: " + cmd.scope.get(4) + ", Steps: " + cmd.minprefix + ".."
                                                + cmd.maxprefix + ", Time: " + duration + "\n");
                                        } else {

                                            /*
                                             Scope: exactly 2 Value, 2 Quorum, exactly 3 Acceptor, exactly 2 Ballot, 8 Message
                                             Label: ChosenValue
                                            */
                                            printWriter.print("\nScope: " + cmd + '\n' + "Label: " + cmd.label + ", Value: " + cmd.scope.get(0)
                                                + ", Quorum: " + cmd.scope.get(1) + ", Acceptors: " + cmd.scope.get(2) + ", Ballot: "
                                                + cmd.scope.get(3) + ", Message: " + cmd.scope.get(4) + ", Steps: " + cmd.minprefix + ".."
                                                + cmd.maxprefix + ", Time: " + duration + "\n");
                                        }
                                        if (duration.equals("Timeout")) {
                                            track(messageType, solver, strategyName, cmd);
                                        }
                                    }

                                    if (protocol.equals("VerticalPaxos")) {
                                        if (messageType.equals("scope-vertical-paxosI-no-message") || messageType.equals("scope-vertical-paxosII-no-message")) { //because there is no messages
                                            /*
                                             Scope: exactly 3 Value, 10 Quorum, exactly 4 Acceptor, exactly 4 Ballot, exactly 2 Leader, exactly 12 Vote
                                             Label: ChosenValue
                                             */
                                            System.out.println(cmd.scope);
                                            printWriter.print("\nScope: " + cmd + '\n' + "Label: " + cmd.label + ", Value: " + cmd.scope.get(0)
                                                + ", Quorum: " + cmd.scope.get(1) + ", Acceptors: " + cmd.scope.get(2) + ", Ballot: "
                                                + cmd.scope.get(3) + ", Leader: " + cmd.scope.get(4) + ", Vote: "
                                                + cmd.scope.get(5) + ", Steps: " + cmd.minprefix + ".."
                                                + cmd.maxprefix + ", Time: " + duration + "\n");
                                        } else {
                                             /*
                                              Scope: exactly 2 Value, 6 Quorum, exactly 3 Acceptor, exactly 3 Ballot, exactly 2 Leader, 9 BasicMessage
                                              Label: ChosenValue
                                             */
                                            printWriter.print("\nScope: " + cmd + '\n' + "Label: " + cmd.label + ", Value: " + cmd.scope.get(0)
                                                + ", Quorum: " + cmd.scope.get(1) + ", Acceptors: " + cmd.scope.get(2) + ", Ballot: "
                                                + cmd.scope.get(3) + ", Leader: " + cmd.scope.get(4)
                                                + ", Message: " + cmd.scope.get(5) + ", Steps: " + cmd.minprefix + ".."
                                                + cmd.maxprefix + ", Time: " + duration + "\n");
                                        }
                                    }
                                }

                                printWriter.close();
                                myFile.close();
                            } catch (IOException e) {
                                printWriter.close();
                                myFile.close();
                                System.out.println("An error occurred.");
                                e.printStackTrace();
                            }
                        }
                    }
                }
            }
        }
        System.out.println("This is the end.");
        System.exit(0);
    }

    public static void track(String messageType, String solver, String strategyName, Command cmd) {
        String key = messageType + solver + strategyName;
        ScopeTracker scopeTracker =
            new ScopeTracker(cmd.maxprefix, cmd.scope.get(0).startingScope, cmd.scope.get(3).startingScope, cmd.scope.get(1).startingScope, solver, strategyName);
        SortedSet<ScopeTracker> sorted = timedoutScope.get(key);
        if (sorted == null) {
            sorted = new TreeSet<>();
            timedoutScope.put(key, sorted);
        }
        sorted.add(scopeTracker);
    }

    public static boolean checkTracked(String messageType, String solver, String strategyName, Command cmd) {
        String key = messageType + solver + strategyName;
        ScopeTracker scopeTracker =
            new ScopeTracker(cmd.maxprefix, cmd.scope.get(0).startingScope, cmd.scope.get(3).startingScope, cmd.scope.get(1).startingScope, solver, strategyName);
        SortedSet<ScopeTracker> sorted = timedoutScope.get(key);
        if (sorted != null) {
             Optional<ScopeTracker> found = sorted.stream().filter(s -> s.otherCompareTo(scopeTracker) == 0 && s.steps < scopeTracker.steps).findAny();
             if (found.isPresent()) {
                 return false;
             }
        }
        return true;
    }
}