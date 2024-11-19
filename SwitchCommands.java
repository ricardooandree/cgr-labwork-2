package net.floodlightcontroller.cgrmodule.util;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.projectfloodlight.openflow.protocol.OFFlowMod;
import org.projectfloodlight.openflow.protocol.OFFlowModCommand;
import org.projectfloodlight.openflow.protocol.OFFlowModFlags;
import org.projectfloodlight.openflow.protocol.OFPacketIn;
import org.projectfloodlight.openflow.protocol.match.*;
import org.projectfloodlight.openflow.protocol.OFPacketOut;
import org.projectfloodlight.openflow.protocol.OFVersion;
import org.projectfloodlight.openflow.protocol.action.OFAction;
import org.projectfloodlight.openflow.protocol.action.OFActionOutput;
import org.projectfloodlight.openflow.protocol.instruction.OFInstruction;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.TableId;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.packet.Ethernet;

public class SwitchCommands 
{
	public static final short NO_TIMEOUT = 0;
	public static final short DEFAULT_PRIORITY = 1;
	public static final short MIN_PRIORITY = Short.MIN_VALUE+1;
	public static final short MAX_PRIORITY = Short.MAX_VALUE-1;
	
	// Interface to the logging system
    private static Logger log =
            LoggerFactory.getLogger(SwitchCommands.class.getSimpleName());

	/**
     * Installs a rule in a switch's flow table.
     * @param sw the switch in which the rule should be installed
     * @param table the table in which the rule should be installed
     * @param priority the priority of the rule; larger values are higher 
     *         priority
     * @param matchCriteria the match criteria for the rule
     * @param instructions to apply to packets matching the rule call with null if Openflow less than 1.1
     * @param actions list to apply to packets matching the rule call with null if Openflow above 1.1
     * @param hardTimeout the rule should be removed after hardTimeout seconds 
     *         have elapsed since the rule was installed; if 0, then the rule
     *         will never be removed
     * @param idleTimeout the rules should be removed after idleTimeout seconds
     *         have elapsed since a packet last matched the rule; if 0, then the
     *         rule will never be removed due to a lack of matching packets
     * @param bufferId apply the newly installed rule to the packet buffered
     *         in this provided slot on the switch
     * @param ReceivedRemoved if true the SEND_FLOW_REM flag is set in the FlowMod message.         
     * @return true if the rule was sent to the switch, otherwise false
     */
    public static boolean installRule(IOFSwitch sw, TableId table, short priority,
            Match matchCriteria, List<OFInstruction> instructions,List<OFAction> actions, 
            short hardTimeout, short idleTimeout, OFBufferId bufferId, boolean ReceivedRemoved)
    {
    	OFFlowMod.Builder rule = sw.getOFFactory().buildFlowAdd();
        rule.setHardTimeout(hardTimeout);
        rule.setIdleTimeout(idleTimeout);
        rule.setPriority(priority);
        rule.setTableId(table);
        rule.setBufferId(bufferId);

        rule.setMatch(matchCriteria);
        if (instructions !=null){
          rule.setInstructions(instructions);
        }  
        else 
        	if (actions!=null){
        		rule.setActions(actions);
        	}
        // if we wan to to receive Flow_Removed Messages for this OpenFlow FlowEntry
		Set<OFFlowModFlags> sfmf = new HashSet<OFFlowModFlags>();
		if (ReceivedRemoved) {
			sfmf.add(OFFlowModFlags.SEND_FLOW_REM);
			rule.setFlags(sfmf);
		}
		
        try
        {
            sw.write(rule.build());
            log.debug("Installing rule: "+rule);
        }
        catch (Exception e)
        {
            log.error("Failed to install rule: "+rule);
            return false;
        }

        return true;
    }
    

    /**
     * Remove a rule from a switch's flow table.
     * @param sw the switch from which the rule should be removed
     * @param table the table from which the rule should be removed
     * @param matchCriteria match criteria specifying the rules to delete (the first rule with a match that is equal to matchCriteria is removed
     * @return true if the delete was sent to the switch, otherwise false
     */
    public static boolean removeRules(IOFSwitch sw, TableId table, 
    		Match matchCriteria)
    {
    	OFFlowMod.Builder rule = sw.getOFFactory().buildFlowDelete();
        rule.setTableId(table);

        rule.setMatch(matchCriteria);
        

        try
        {
            sw.write(rule.build());
            log.debug("Removing rule: "+rule);
        }
        catch (Exception e)
        {
            log.error("Failed to remove rule: "+rule);
            return false;
        }

        return true;
    }
    
	/**
	 * Sends a packet out of a switch build from an Ethernet object.
	 * @param outSw the switch out which the packet should be forwarded
	 * @param outPort the switch port out which the packet should be forwarded
	 * @param eth the Ethernet packet to forward 
	 * @return true if the packet was sent to the switch, otherwise false
	 */
	public static boolean sendPacketOut(IOFSwitch outSw, OFPort outPort, 
			Ethernet eth) 
    {
		
		// Create an OFPacketOut for the packet
		OFPacketOut.Builder pktOut = outSw.getOFFactory().buildPacketOut();
              
        // Update the buffer ID
        pktOut.setBufferId(OFBufferId.NO_BUFFER);
                
        // Set the actions to apply for this packet
        List<OFAction> actions = new ArrayList<OFAction>();
        OFAction.Builder action = outSw.getOFFactory().actions().buildOutput().setPort(outPort).setMaxLen(0xffFFffFF);
        actions.add(action.build());
		
        pktOut.setActions(actions);       
        // Set packet data
        byte[] packetData = eth.serialize();
        pktOut.setData(packetData);
        
        // Send the packet to the switch
        try 
        {
            outSw.write(pktOut.build());
           // log.info("Forwarding packet out: "+eth.toString() + "to Switch: " + outSw );
        }
        catch (Exception e) 
        {
        	log.error("Failed to forward packet: "+eth.toString() + "to Switch: " + outSw);
			return false;
        }
        
        return true;
	}
	/**
	 * Sends a packet out of a switch built from a received Packet_In.
	 * @param outSw the switch out which the packet should be forwarded
	 * @param outPort the switch port out which the packet should be forwarded
	 * @param pi the received packet_in to forward 
	 * @return true if the packet was sent to the switch, otherwise false
	 */
	public static boolean sendPacketOutPacketIn(IOFSwitch outSw, OFPort outPort, 
			OFPacketIn pi) 
    {
		OFPort inPort = (pi.getVersion().compareTo(OFVersion.OF_12) < 0 ? pi.getInPort() : pi.getMatch().get(MatchField.IN_PORT));
		// The assumption here isn that (outSw) is the switch that generated the
				// packet-in. If the input port is the same as output port, then
				// the packet-out should be ignored.
				if (inPort.equals(outPort)) {
					if (log.isDebugEnabled()) {
						log.debug("Attempting to do packet-out to the same " +
								"interface as packet-in. Dropping packet. " +
								" SrcSwitch={}, match = {}, pi={}",
								new Object[]{outSw, pi.getMatch(), pi});
						return false;
					}
				}
				
		// Create an OFPacketOut for the packet
		OFPacketOut.Builder pktOut = outSw.getOFFactory().buildPacketOut();
              
        // Update the buffer ID
        pktOut.setBufferId(OFBufferId.NO_BUFFER);
        //Set the Inport of the Packet Out to the same value as the packet In to ensure proper FLOOD action behaviour
        pktOut.setInPort(inPort);
                
        // Set the actions to apply for this packet
        List<OFAction> actions = new ArrayList<OFAction>();
        OFAction.Builder action = outSw.getOFFactory().actions().buildOutput().setPort(outPort).setMaxLen(0xffFFffFF);
        actions.add(action.build());
		
        pktOut.setActions(actions);       
        // Set packet data
        byte[] packetData = pi.getData();
        pktOut.setData(packetData);
        OFPacketOut po = pktOut.build();
        
        // Send the packet to the switch
        try 
        {	
        	
            outSw.write(po);
            //log.info("Forwarding packet out: "+po.toString() + "to Switch: " + outSw );
        }
        catch (Exception e) 
        {
        	log.error("Failed to forward packet: "+po.toString() + "to Switch: " + outSw + "Exception: " + e);
			return false;
        }
        
        return true;
	}
}
