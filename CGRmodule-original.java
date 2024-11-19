package net.floodlightcontroller.cgrmodule;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.projectfloodlight.openflow.protocol.OFFlowMod;
import org.projectfloodlight.openflow.protocol.OFFlowModCommand;
import org.projectfloodlight.openflow.protocol.OFFlowModFlags;
import org.projectfloodlight.openflow.protocol.OFFlowRemoved;
import org.projectfloodlight.openflow.protocol.OFMessage;
import org.projectfloodlight.openflow.protocol.OFPacketIn;
import org.projectfloodlight.openflow.protocol.OFPacketOut;
import org.projectfloodlight.openflow.protocol.OFPortDesc;
import org.projectfloodlight.openflow.protocol.OFType;
import org.projectfloodlight.openflow.protocol.OFVersion;
import org.projectfloodlight.openflow.protocol.action.OFAction;
import org.projectfloodlight.openflow.protocol.action.OFActionOutput;
import org.projectfloodlight.openflow.protocol.action.OFActions;
import org.projectfloodlight.openflow.protocol.instruction.OFInstruction;
import org.projectfloodlight.openflow.protocol.instruction.OFInstructionApplyActions;
import org.projectfloodlight.openflow.protocol.instruction.OFInstructions;
import org.projectfloodlight.openflow.protocol.match.Match;
import org.projectfloodlight.openflow.protocol.match.MatchField;
import org.projectfloodlight.openflow.types.DatapathId;
import org.projectfloodlight.openflow.types.MacAddress;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.OFVlanVidMatch;
import org.projectfloodlight.openflow.types.TableId;
import org.projectfloodlight.openflow.types.U64;
import org.projectfloodlight.openflow.types.VlanVid;
import org.projectfloodlight.openflow.util.LRULinkedHashMap;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import net.floodlightcontroller.cgrmodule.util.*;
import net.floodlightcontroller.core.FloodlightContext;
import net.floodlightcontroller.core.IControllerCompletionListener;
import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFMessageListener;
import net.floodlightcontroller.core.IOFSwitchListener;
import net.floodlightcontroller.core.PortChangeType;
import net.floodlightcontroller.core.internal.IOFSwitchService;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.learningswitch.LearningSwitch;
import net.floodlightcontroller.packet.Ethernet;
import net.floodlightcontroller.util.OFMessageUtils;

public class CGRmodule implements IFloodlightModule, IOFMessageListener, IOFSwitchListener {
	protected static Logger log = LoggerFactory.getLogger(CGRmodule.class);

	// Module dependencies
	protected IFloodlightProviderService floodlightProviderService;
	protected IOFSwitchService switchService;

	// Stores the learned state for each switch
	protected Map<IOFSwitch, Map<MacAddress, OFPort>> macToSwitchPortMap;
	
	// flow-mod - for use in the cookie
	public static final int LEARNING_SWITCH_APP_ID = 1;
	// LOOK! This should probably go in some class that encapsulates
	// the app cookie management
	public static final int APP_ID_BITS = 12;
	public static final int APP_ID_SHIFT = (64 - APP_ID_BITS);
	public static final long LEARNING_SWITCH_COOKIE = (long) (LEARNING_SWITCH_APP_ID & ((1 << APP_ID_BITS) - 1)) << APP_ID_SHIFT;

	// more flow-mod defaults
	protected static short FLOWMOD_DEFAULT_IDLE_TIMEOUT = 5; // in seconds
	protected static short FLOWMOD_DEFAULT_HARD_TIMEOUT = 0; // infinite
	protected static short FLOWMOD_PRIORITY = 100;

	// for managing our map sizes
	protected static final int MAX_MACS_PER_SWITCH  = 1000;

	// normally, setup reverse flow as well. Disable only for using cbench for comparison with NOX etc.
	protected static final boolean LEARNING_SWITCH_REVERSE_FLOW = true;
	

	/**
	 * @param floodlightProvider the floodlightProvider to set
	 */
	public void setFloodlightProvider(IFloodlightProviderService floodlightProviderService) {
		this.floodlightProviderService = floodlightProviderService;
	}

	@Override
	public String getName() {
		return "CGRModule";
	}

	/**
	 * Adds a host to the MAC->SwitchPort mapping
	 * @param sw The switch to add the mapping to
	 * @param mac The MAC address of the host to add
	 * @param portVal The switchport that the host is on
	 */
	protected void addToPortMap(IOFSwitch sw, MacAddress mac, OFPort portVal) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);

		if (swMap == null) {
			swMap = new LRULinkedHashMap<MacAddress, OFPort>(MAX_MACS_PER_SWITCH);
			macToSwitchPortMap.put(sw, swMap);
		}
		swMap.put(mac, portVal);
	}

	/**
	 * Removes a host from the MAC->SwitchPort mapping
	 * @param sw The switch to remove the mapping from
	 * @param mac The MAC address of the host to remove
	 */
	protected void removeFromPortMap(IOFSwitch sw, MacAddress mac) {

		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			swMap.remove(mac);
		}
	}

	/**
	 * Get the port that a MAC is associated with
	 * @param sw The switch to get the mapping from
	 * @param mac The MAC address to get
	 * @return The port the host is on
	 */
	public OFPort getFromPortMap(IOFSwitch sw, MacAddress mac) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			return swMap.get(mac);
		}

		// if none found
		return null;
	}

	/**
	 * Clears the MAC -> SwitchPort map for all switches
	 */
	public void clearLearnedTable() {
		macToSwitchPortMap.clear();
	}

	/**
	 * Clears the MAC/VLAN -> SwitchPort map for a single switch
	 * @param sw The switch to clear the mapping for
	 */
	public void clearLearnedTable(IOFSwitch sw) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			swMap.clear();
		}
	}
	
	protected Match createMatchFromPacket(IOFSwitch sw, OFPort inPort, Ethernet eth) {
		// The packet in match will only contain the port number.
		// We need to add in specifics for the hosts we're routing between.
		MacAddress srcMac = eth.getSourceMACAddress();
		MacAddress dstMac = eth.getDestinationMACAddress();

		Match.Builder mb = sw.getOFFactory().buildMatch();
		mb.setExact(MatchField.IN_PORT, inPort)
		.setExact(MatchField.ETH_SRC, srcMac)
		.setExact(MatchField.ETH_DST, dstMac);
		return mb.build();
	}

	/**
	 * Processes a OFPacketIn message. If the switch has learned the MAC to port mapping
	 * for the pair it will write a FlowMod for. If the mapping has not been learned the
	 * we will flood the packet.
	 * @param sw
	 * @param pi
	 * @param cntx
	 * @return
	 */
	private Command processPacketInMessage(IOFSwitch sw, OFPacketIn pi, FloodlightContext cntx) {
		OFPort inPort = (pi.getVersion().compareTo(OFVersion.OF_12) < 0 ? pi.getInPort() : pi.getMatch().get(MatchField.IN_PORT));
		
		/*Read the Packet_In Message Payload (EThernet packet) in to an Ethernet Object*/
		Ethernet eth = IFloodlightProviderService.bcStore.get(cntx, IFloodlightProviderService.CONTEXT_PI_PAYLOAD);
		/* Read packet header attributes into a Match object */
		MacAddress sourceMac = eth.getSourceMACAddress();
		MacAddress destMac = eth.getDestinationMACAddress();

		if (sourceMac == null) {
			sourceMac = MacAddress.NONE;
		}
		if (destMac == null) {
			destMac = MacAddress.NONE;
		}
		
		if ((destMac.getLong() & 0xfffffffffff0L) == 0x0180c2000000L) {
			if (log.isTraceEnabled()) {
				log.trace("ignoring packet addressed to 802.1D/Q reserved addr: switch {} dest MAC {}",
						new Object[]{ sw, destMac.toString() });
			}
			return Command.STOP;
		}


		if ((!sourceMac.isBroadcast())&&(!sourceMac.isMulticast())) {
			log.info("Unicast packet received: switch {} Ethertype {}",
					new Object[]{ sw, eth.getEtherType() });
		  // If source MAC is a unicast address, learn the port for this MAC/VLAN
			
		}
		//check if port for destination MAC is known
		// If so output flow-mod and/or packet
		
		//for now it floods trough all ports like a hub. 
		SwitchCommands.sendPacketOutPacketIn(sw, OFPort.FLOOD, pi);
	    // Add flow table entry matching source MAC, dest MAC and input port
		// that sends to the port we previously learned for the dest MAC.  Also
		// add a flow table entry with source and destination MACs reversed, and
		// input and output ports reversed.  When either entry expires due to idle
		// timeout, remove the other one.  This ensures that if a device moves to
		// a different port, a constant stream of packets headed to the device at
		// its former location does not keep the stale entry alive forever.
		// We write FlowMods with Buffer ID none then explicitly PacketOut the buffered packet
		
		// to send the packet in back as a packet out to the previously learned port outPort use;
		//SwitchCommands.sendPacketOutPacketIn(outSw, outPort, pi)
		
		// you should then write the flow mod using SwitchCommands install rule method since it receives either instructions or actions
		// depending on the OpenFlow Version you should do the following:
	/*	
		OFActions actions = sw.getOFFactory().actions(); //actions builder
		List<OFAction> al = new ArrayList<OFAction>();
		OFActionOutput output = actions.buildOutput()
				.setPort(outPort)    // outPort is the port trough which the sw should send the Matching Packets
				.setMaxLen(0xffFFffFF)
				.build();
		al.add(output);
	
		if (pi.getVersion().compareTo(OFVersion.OF_13)==0){
				OFInstructions instructions =  sw.getOFFactory().instructions(); //instructions builder
				OFInstructionApplyActions applyActions = instructions.buildApplyActions().setActions(al).build(); //use the instructions builder to build an applyActions instruction with the given action list. 
				ArrayList<OFInstruction> instructionList = new ArrayList<OFInstruction>(); 
				instructionList.add(applyActions); //add the applyActions Instruction to the Instruction list
				SwitchCommands.installRule(sw, TableId.of(0), CGRL2Switch.FLOWMOD_PRIORITY, match, instructionList, null, CGRL2Switch.FLOWMOD_DEFAULT_HARD_TIMEOUT, CGRL2Switch.FLOWMOD_DEFAULT_IDLE_TIMEOUT, OFBufferId.NO_BUFFER);
		} else SwitchCommands.installRule(sw, TableId.of(0), CGRL2Switch.FLOWMOD_PRIORITY, match, null, al, CGRL2Switch.FLOWMOD_DEFAULT_HARD_TIMEOUT, CGRL2Switch.FLOWMOD_DEFAULT_IDLE_TIMEOUT, OFBufferId.NO_BUFFER);
*/
			
		//
		return Command.STOP;
	}

	/**
	 * Processes a flow removed message. 
	 * @param sw The switch that sent the flow removed message.
	 * @param flowRemovedMessage The flow removed message.
	 * @return Whether to continue processing this message or stop.
	 */
	private Command processFlowRemovedMessage(IOFSwitch sw, OFFlowRemoved flowRemovedMessage) {
		if (log.isTraceEnabled()) {
			log.trace("{} flow entry removed {}", sw, flowRemovedMessage);
		}
		Match match = flowRemovedMessage.getMatch();
		// When a flow entry expires, it means the device with the matching source
		// MAC address either stopped sending packets or moved to a different
		// port.  If the device moved, we can't know where it went until it sends
		// another packet, allowing us to re-learn its port.  Meanwhile we remove
		// it from the macToPortMap to revert to flooding packets to this device.
		
		// Also, if packets keep coming from another device (e.g. from ping), the
		// corresponding reverse flow entry will never expire on its own and will
		// send the packets to the wrong port (the matching input port of the
		// expired flow entry), so we must delete the reverse entry explicitly.
		
		return Command.CONTINUE;
	}

	// IOFMessageListener

	@Override
	public Command receive(IOFSwitch sw, OFMessage msg, FloodlightContext cntx) {
		switch (msg.getType()) {
		case PACKET_IN:
			return this.processPacketInMessage(sw, (OFPacketIn) msg, cntx);
		case FLOW_REMOVED:
			return this.processFlowRemovedMessage(sw, (OFFlowRemoved) msg);
		case ERROR:
			log.info("received an error {} from switch {}", msg, sw);
			return Command.CONTINUE;
		default:
			log.error("received an unexpected message {} from switch {}", msg, sw);
			return Command.CONTINUE;
		}
	}

	@Override
	public boolean isCallbackOrderingPrereq(OFType type, String name) {
		return false;
	}

	@Override
	public boolean isCallbackOrderingPostreq(OFType type, String name) {
		return (type.equals(OFType.PACKET_IN) && name.equals("forwarding")) ;
	}
	
	// IFloodlightModule

    /**
     * Tell the module system which services we provide.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleServices() 
	{ return null; }

	/**
     * Tell the module system which services we implement.
     */
	@Override
	public Map<Class<? extends IFloodlightService>, IFloodlightService> 
			getServiceImpls() 
	{ return null; }

	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleDependencies() {
		Collection<Class<? extends IFloodlightService>> l =
				new ArrayList<Class<? extends IFloodlightService>>();
		l.add(IFloodlightProviderService.class);
		return l;
	}

	@Override
	public void init(FloodlightModuleContext context) throws FloodlightModuleException {
		macToSwitchPortMap = new ConcurrentHashMap<IOFSwitch, Map<MacAddress, OFPort>>();
		floodlightProviderService = context.getServiceImpl(IFloodlightProviderService.class);
		this.switchService = context.getServiceImpl(IOFSwitchService.class);
		log.info("CGR module started {}");
	}

	@Override
	public void startUp(FloodlightModuleContext context) {
		// paag: register the IControllerCompletionListener
		floodlightProviderService.addOFMessageListener(OFType.PACKET_IN, this);
		floodlightProviderService.addOFMessageListener(OFType.FLOW_REMOVED, this);
		floodlightProviderService.addOFMessageListener(OFType.ERROR, this);
		switchService.addOFSwitchListener(this);

		// read our config options
		Map<String, String> configOptions = context.getConfigParams(this);
		try {
			String idleTimeout = configOptions.get("idletimeout");
			if (idleTimeout != null) {
				FLOWMOD_DEFAULT_IDLE_TIMEOUT = Short.parseShort(idleTimeout);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow idle timeout, " +
					"using default of {} seconds", FLOWMOD_DEFAULT_IDLE_TIMEOUT);
		}
		try {
			String hardTimeout = configOptions.get("hardtimeout");
			if (hardTimeout != null) {
				FLOWMOD_DEFAULT_HARD_TIMEOUT = Short.parseShort(hardTimeout);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow hard timeout, " +
					"using default of {} seconds", FLOWMOD_DEFAULT_HARD_TIMEOUT);
		}
		try {
			String priority = configOptions.get("priority");
			if (priority != null) {
				FLOWMOD_PRIORITY = Short.parseShort(priority);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow priority, " +
					"using default of {}",
					FLOWMOD_PRIORITY);
		}
		log.debug("FlowMod idle timeout set to {} seconds", FLOWMOD_DEFAULT_IDLE_TIMEOUT);
		log.debug("FlowMod hard timeout set to {} seconds", FLOWMOD_DEFAULT_HARD_TIMEOUT);
		log.debug("FlowMod priority set to {}", FLOWMOD_PRIORITY);
	}

	@Override
	public void switchAdded(DatapathId switchId) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void switchRemoved(DatapathId switchId) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void switchActivated(DatapathId switchId) {
		// TODO Auto-generated method stub
		/// Initial FlowMod rules can be installed here upon switch activation.
		
	}

	@Override
	public void switchPortChanged(DatapathId switchId, OFPortDesc port, PortChangeType type) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void switchChanged(DatapathId switchId) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void switchDeactivated(DatapathId switchId) {
		// TODO Auto-generated method stub
		
	}

}

