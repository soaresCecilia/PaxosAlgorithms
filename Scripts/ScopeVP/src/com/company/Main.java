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
            FileWriter myFileVPIDynamicMsg = new FileWriter(basePath + "VerticalPaxos/VPI/scope-vertical-paxosI-dynamic-message.als");
            FileWriter myFileVPINoMsg = new FileWriter(basePath + "VerticalPaxos/VPI/scope-vertical-paxosI-no-message.als");
            FileWriter myFileVPIMsgBox = new FileWriter(basePath + "VerticalPaxos/VPI/scope-vertical-paxosI-static-message.als");
            FileWriter myFileVPIIDynamicMsg = new FileWriter(basePath + "VerticalPaxos/VPII/scope-vertical-paxosII-dynamic-message.als");
            FileWriter myFileVPIINoMsg = new FileWriter(basePath + "VerticalPaxos/VPII/scope-vertical-paxosII-no-message.als");
            FileWriter myFileVPIIMsgBox = new FileWriter(basePath + "VerticalPaxos/VPII/scope-vertical-paxosII-static-message.als");


            PrintWriter printWriterVPIDynamicMsg = new PrintWriter(myFileVPIDynamicMsg);
            PrintWriter printWriterVPINoMsg = new PrintWriter(myFileVPINoMsg);
            PrintWriter printWriterVPIIDynamicMsg = new PrintWriter(myFileVPIIDynamicMsg);
            PrintWriter printWriterVPIINoMsg = new PrintWriter(myFileVPIINoMsg);
            PrintWriter printWriterVPIMsgBox = new PrintWriter(myFileVPIMsgBox);
            PrintWriter printWriterVPIIMsgBox = new PrintWriter(myFileVPIIMsgBox);

            printWriterVPIDynamicMsg.print("/****************TESTING DIFFERENT SCOPES VPI : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open dynamicMessages " + "\n \n" );

            printWriterVPINoMsg.print("/****************TESTING DIFFERENT SCOPES VPI : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open noMessages " + "\n \n" );

            printWriterVPIIDynamicMsg.print("/****************TESTING DIFFERENT SCOPES VPII : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open dynamicMessages " + "\n \n" );

            printWriterVPIINoMsg.print("/****************TESTING DIFFERENT SCOPES VPII : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open noMessages " + "\n \n" );

            printWriterVPIMsgBox.print("/****************TESTING DIFFERENT SCOPES VPI : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open staticMessages " + "\n \n" );

            printWriterVPIIMsgBox.print("/****************TESTING DIFFERENT SCOPES VPII : ACCEPTORS : 3-4 : ********************/"
                    + "\n \n" + "open staticMessages " + "\n \n" );

            int vp1messages = 0;
            int vp1Nomessages = 0;



            //leader = 2 because is the minimum ballot
            int leader = 2;
            int initialStep = 0;

            //VP1

            //VPI 3 Acceptors - initialStep = 10 finalStep = 30
            //VPI 4 Acceptors - initialStep = 11 finalStep = 33

            for (int acceptor = 3; acceptor <= 4; acceptor++) {
                for(int value = 2; value <= 3; value++) {
                    for(int ballot = 3; ballot <= 4; ballot++) {
                        for(int quorum = (2 * ballot); quorum <= (2 * ballot) + 2; quorum = quorum + 2) {
                            if(acceptor == 3) {
                                initialStep = 10;
                            }
                            else if (acceptor == 4){
                                initialStep = 11;
                            }
                            else {
                                System.out.println("Number of acceptors not valid");
                            }
                            for (int step = initialStep; step <= (initialStep + 5); step = step + 5) {
                                vp1messages++;
                                String s1 = "check ChosenValue for exactly " + value + " Value, exactly " + quorum + " Quorum, exactly " +
                                        acceptor + " Acceptor, exactly " + ballot + " Ballot, exactly " + leader + " Leader, " +
                                        (step - 1) + " BasicMessage, " + step + ".." + step + " steps\n\n";
                                printWriterVPIDynamicMsg.print(s1);
                                printWriterVPIMsgBox.print(s1);
                            }
                            for (int step = initialStep; step <= (3 * initialStep); step = step + 5) {
                                vp1Nomessages++;
                                String s2 = "check ChosenValue for exactly " + value + " Value, exactly " + quorum + " Quorum, exactly " +
                                        acceptor + " Acceptor, exactly " + ballot + " Ballot, exactly " + leader + " Leader, " +
                                        "exactly " + (ballot * value) + " Vote, " + step + ".." + step + " steps\n\n";
                                printWriterVPINoMsg.print(s2);
                            }
                        }
                    }
                }
            }

            int vp2messages = 0;
            int vp2Nomessages = 0;


            //VP2

            //VPII 3 Acceptors - initialStep = 9 finalStep = 27
            //VPII 4 Acceptors - initialStep = 10 finalStep = 30

            for (int acceptor = 3; acceptor <= 4; acceptor++) {
                for(int value = 2; value <= 3; value++) {
                    for(int ballot = 3; ballot <= 4; ballot++) {
                        for(int quorum = (2 * ballot); quorum <= (2 * ballot) + 2; quorum = quorum + 2) {
                            if(acceptor == 3) {
                                initialStep = 9;
                            }
                            else if (acceptor == 4){
                                initialStep = 10;
                            }
                            else {
                                System.out.println("Number of acceptors not valid");
                            }
                            for (int step = initialStep; step <= (initialStep + 5); step = step + 5) {
                                vp2messages++;
                                String s1 = "check ChosenValue for exactly " + value + " Value, exactly " + quorum + " Quorum, exactly " +
                                        acceptor + " Acceptor, exactly " + ballot + " Ballot, exactly " + leader + " Leader, " +
                                        (step - 1) + " BasicMessage, " + step + ".." + step + " steps\n\n";
                                printWriterVPIIDynamicMsg.print(s1);
                                printWriterVPIIMsgBox.print(s1);
                            }
                            for (int step = initialStep; step <= (3 * initialStep); step = step + 5) {
                                vp2Nomessages++;
                                String s2 = "check ChosenValue for exactly " + value + " Value, exactly " + quorum + " Quorum, exactly " +
                                        acceptor + " Acceptor, exactly " + ballot + " Ballot, exactly " + leader + " Leader, " +
                                        "exactly " + (ballot * value) + " Vote, " + step + ".." + step + " steps\n\n";
                                printWriterVPIINoMsg.print(s2);
                            }
                        }
                    }
                }
            }

            System.out.println("Total scopes vp1Messages " + vp1messages);
            System.out.println("Total scopes vp2Messages " + vp2messages);
            System.out.println("Total scopes vp1NoMessages " + vp1Nomessages);
            System.out.println("Total scopes vp2NoMessages " + vp2Nomessages);

            printWriterVPIDynamicMsg.close();
            printWriterVPIIDynamicMsg.close();
            printWriterVPINoMsg.close();
            printWriterVPIINoMsg.close();
            printWriterVPIMsgBox.close();
            printWriterVPIIMsgBox.close();

        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
    }
}

