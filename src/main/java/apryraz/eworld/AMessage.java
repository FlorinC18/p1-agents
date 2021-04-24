package apryraz.eworld;

/**
*  Class for representing messages exchanged between agents and the
*  World interface object
**/
public class AMessage {
  /*
  *  Array of String objects, that represent the different fields of each message
  *  So far, we assume a fixed pattern, with always three fields in any message:
  *  field0:  message type: moveto, movedto, notmovedto, detects at, yes/no ...
  *  field1:  first parameter of message
  *  field2:  second parameter of message
  */
 String[] msg ;

/**
*  Class constructor
*
*  @param msgtype  message type
*  @param par1:  first parameter of message
*  @param par2:  second parameter of message
   @param par3:  third parameter of message
**/
 public  AMessage( String msgtype, String par1, String par2, String par3 ) {
   msg = new String[4];

   msg[0] = msgtype;
   msg[1] = par1;
   msg[2] = par2;
   msg[3] = par3;
 }

 /**
 *  Show message on screen
 **/
 public void showMessage() {
     System.out.println( "MESSAGE: "+msg[0]+ " "+ msg[1] + " "+ msg[2]+ " "+msg[3] );
 }

 /**
 *  get some part of the message
 *
 * @param c index of the component to return
 *
 * @return the String corresponding to the component requested
 **/
 public String getComp(int c) {
   return msg[c];
 }

}
