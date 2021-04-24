import java.util.ArrayList;
import java.util.Iterator;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import static java.lang.System.exit;

import org.sat4j.specs.*;
import org.sat4j.minisat.*;
import org.sat4j.reader.*;


import apryraz.eworld.*;

import static org.junit.Assert.assertEquals;
import org.junit.*;

/**
*  Class for testing the TreasureFinder agent
**/
public class EnvelopeFinderTest {


 /**
 *  This function should execute the next step of the agent, and the assert
 *  whether the resulting state is equal to the targetState
 *
 *  @param eAgent       EnvelopeFinder agent
 *  @param targetState  the state that should be equal to the resulting state of
 *                      the agent after performing the next step
 **/
  public void testMakeSimpleStep(  EnvelopeFinder eAgent,
                                   EFState targetState )  throws
                                           IOException,  ContradictionException, TimeoutException {
    // Check (assert) whether the resulting state is equal to
    //  the targetState after performing action runNextStep with bAgent

  }


/**
*  Read an state from the current position of the file trough the
*  BufferedReader object
*
*  @param br BufferedReader object interface to the opened file of states
*  @param wDim dimension of the world
**/
  public EFState readTargetStateFromFile( BufferedReader br, int wDim )  throws
          IOException {
       EFState efstate = new EFState(wDim);
       String row;
       String[] rowvalues;

       for (int i = wDim; i >= 1; i--) {
           row = br.readLine();
           rowvalues = row.split(" ");
           for (int j = 1; j <= wDim; j++) {
              efstate.set(i,j,rowvalues[j-1]);
           }
        }
        return efstate;
  }

/**
*  Load a sequence of states from a file, and return the list
*
*  @param wDim        dimension of the world
*  @param numStates   num of states to read from the file
*  @param statesFile file name with sequence of target states, that should
*                      be the resulting states after each movement in fileSteps
*
*  @return returns an ArrayList of TFState with the resulting list of states
**/
  ArrayList<EFState> loadListOfTargetStates( int wDim, int numStates, String statesFile ) {

     ArrayList<EFState> listOfStates = new ArrayList<EFState>(numStates);

     try {
         BufferedReader br = new BufferedReader(new FileReader(statesFile));
         String row;

         // steps = br.readLine();
         for (int s = 0; s < numStates ; s++ ) {
           listOfStates.add(readTargetStateFromFile(br,wDim));
            // Read a blank line between states
            row = br.readLine();
         }
         br.close();
     } catch (FileNotFoundException ex) {
         System.out.println("MSG.   => States file not found");
         exit(1);
     } catch (IOException ex) {
         Logger.getLogger(EnvelopeFinderTest.class.getName()).log(Level.SEVERE, null, ex);
         exit(2);
     }

     return listOfStates;
  }


  /**
  *   This function should run the sequence of steps stored in the file fileSteps,
  *   but only up to numSteps steps.
  *
  *   @param wDim the dimension of world
  *   @param numSteps num of steps to perform
  *   @param fileSteps file name with sequence of steps to perform
  *   @param fileStates file name with sequence of target states, that should
  *                      be the resulting states after each movement in fileSteps
  *   @param fileEnvelopes
  *
  **/
  public void testMakeSeqOfSteps( int wDim,
                                  int numSteps, String fileSteps, String fileStates,
                                  String fileEnvelopes  ) 
       throws   IOException,  ContradictionException, TimeoutException {
      // You should make TreasureFinder and TreasureWorldEnv objects to  test.
      // Then load sequence of target states, load sequence of steps into the eAgent
      // and then test the sequence calling testMakeSimpleStep once for each step.
     EnvelopeFinder eAgent  ;
     // load information about the World into the EnvAgent
     EnvelopeWorldEnv envAgent  ;
     // Load list of states
     ArrayList<EFState> seqOfStates ;


     // Set environment agent and load list of steps into the finder agent
     eAgent.loadListOfSteps(  numSteps, fileSteps ) ;
     eAgent.setEnvironment( envAgent );
  
     // Test here the sequence of steps and check the resulting states with the
     // ones in seqOfStates
  }

  /**
  *   This is an example test. You must replicate this method for each different
  *    test sequence, or use some kind of parametric tests with junit
  **/
  @Test public void TWorldTest1()   throws
          IOException,  ContradictionException, TimeoutException {
   // Example test for 4x4 world , Treasure at 3,3 and 5 steps
    testMakeSeqOfSteps(  4, 5, "tests/steps1.txt", "tests/states1.txt", "tests/envelopes1.txt"  );
  }

}
