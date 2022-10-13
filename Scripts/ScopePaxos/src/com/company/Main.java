package com.company;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class Main {

    public static void main(String[] args) {
        String basePath = System.getProperty("user.dir") + "/";
        
        if (args.length != 0) {
            basePath = args[0];
        }

        System.out.println("Base path: " + basePath);
        try {
            FileWriter myFilePaxosDynamicMsg = new FileWriter(basePath + "Paxos/scope-paxos-dynamic-message.als");
            FileWriter myFilePaxosNoMsg = new FileWriter(basePath + "Paxos/scope-paxos-no-message.als");
            FileWriter myFilePaxosMsgBox = new FileWriter(basePath + "Paxos/scope-paxos-static-message.als");
            PrintWriter printWriterPaxosDynamicMsg = new PrintWriter(myFilePaxosDynamicMsg);
            PrintWriter printWriterPaxosNoMsg = new PrintWriter(myFilePaxosNoMsg);
            PrintWriter printWriterPaxosMsgBox = new PrintWriter(myFilePaxosMsgBox);

            printWriterPaxosDynamicMsg.print("/****************TESTING DIFFERENT SCOPES PAXOS : ACCEPTORS : 3-4 : ********************/"
                            + "\n \n" + "open dynamicMessages " + "\n \n" );

            printWriterPaxosNoMsg.print("/****************TESTING DIFFERENT SCOPES PAXOS : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open noMessages " + "\n \n" );

            printWriterPaxosMsgBox.print("/****************TESTING DIFFERENT SCOPES PAXOS : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open staticMessages " + "\n \n" );

            int nMsg = 0;
            for (int acceptor = 3; acceptor <= 4; acceptor++) {
                for(int value = 2; value <= 3; value++) {
                    for(int ballot = 2; ballot <= 3; ballot++) {
                        for(int quorum = 2; quorum <= 3; quorum++) {
                            int initialStep = (acceptor * 2) + 3;
                            for (int steps = initialStep; steps <= (initialStep + 2); steps = steps + 2) {
                                nMsg++;
                                String s1 = "check ChosenValue for exactly " + value + " Value, " + quorum + " Quorum, exactly " + acceptor +
                                        " Acceptor, exactly " + ballot + " Ballot, " + (steps - 1) + " Message, " + steps + ".." +
                                        steps + " steps\n\n";
                                printWriterPaxosDynamicMsg.print(s1);
                                printWriterPaxosMsgBox.print(s1);
                            }
                        }
                    }
               }
            }

            int nNoMsg = 0;
            for (int acceptor = 3; acceptor <= 4; acceptor++) {
                for(int value = 2; value <= 3; value++) {
                    for(int ballot = 2; ballot <= 3; ballot++) {
                        for(int quorum = 2; quorum <= 3; quorum++) {
                            int initialStep = (acceptor * 2) + 3;
                            for (int steps = initialStep; steps <= (initialStep * 2) + 1; steps = steps + 2) {
                                nNoMsg++;
                                printWriterPaxosNoMsg.print("check ChosenValue for exactly " + value + " Value, " + quorum + " Quorum, exactly " +
                                        acceptor + " Acceptor, exactly " + ballot + " Ballot, exactly " + (ballot * value) + " Vote, " +
                                        steps + ".." + steps + " steps\n\n");
                            }
                        }
                    }
                }
            }

            System.out.println("Total scopes no Message " + nNoMsg);
            System.out.println("Total scopes Message " + nMsg);

            printWriterPaxosDynamicMsg.close();
            printWriterPaxosNoMsg.close();
            printWriterPaxosMsgBox.close();

        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
    }
}
