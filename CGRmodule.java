package net.floodlightcontroller.cgrmodule;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
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
import org.projectfloodlight.openflow.types.EthType;
import org.projectfloodlight.openflow.types.IPv4Address;
import org.projectfloodlight.openflow.types.IpProtocol;
import org.projectfloodlight.openflow.types.MacAddress;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.OFVlanVidMatch;
import org.projectfloodlight.openflow.types.TableId;
import org.projectfloodlight.openflow.types.TransportPort;
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
import net.floodlightcontroller.packet.IPv4;
import net.floodlightcontroller.packet.TCP;
import net.floodlightcontroller.util.OFMessageUtils;

public class CGRmodule implements IFloodlightModule, IOFMessageListener, IOFSwitchListener {
	protected static Logger log = LoggerFactory.getLogger(CGRmodule.class);

	// Module dependencies
	protected IFloodlightProviderService floodlightProviderService;
	protected IOFSwitchService switchService;

	// Stores the learned state for each switch
	protected Map<IOFSwitch, Map<MacAddress, OFPort>> macToSwitchPortMap;
	protected Map<IOFSwitch, Map<MacAddress, Integer>> hostConnectionsMap;  // key = host MAC Address / value = number of active connections
	protected Map<MacAddress, Integer> hostMaxConnectionsMap;				// key = host MAC Address / value = host connections limit
	private FileWriter tcpFlowStatsWriter;									// File writer object
	
	// flow-mod - for use in the cookie
	public static final int LEARNING_SWITCH_APP_ID = 1;

	// LOOK! This should probably go in some class that encapsulates
	// the app cookie management
	public static final int APP_ID_BITS = 12;
	public static final int APP_ID_SHIFT = (64 - APP_ID_BITS);
	public static final long LEARNING_SWITCH_COOKIE = (long) (LEARNING_SWITCH_APP_ID & ((1 << APP_ID_BITS) - 1)) << APP_ID_SHIFT;

	// more flow-mod defaults
	protected static short FLOWMOD_DEFAULT_IDLE_TIMEOUT = 5;   // in seconds -- quando um switch nao recebe pacotes que ativem a regra durante x tempo faz timeout
	protected static short FLOWMOD_DEFAULT_HARD_TIMEOUT = 0;  // infinito - ao fim deste tempo faz hard timeout/drop da regra
	protected static short FLOWMOD_PRIORITY = 100;

	// for managing our map sizes
	protected static final int MAX_MACS_PER_SWITCH  = 1000;

	// normally, setup reverse flow as well. Disable only for using cbench for comparison with NOX etc.
	protected static final boolean LEARNING_SWITCH_REVERSE_FLOW = true;
	
	// Checks if a specific host has connection limitations
	private boolean isConnectionLimited(MacAddress hostMac){
		return hostMaxConnectionsMap.containsKey(hostMac);
	}

	// Checks if a host can connect to another
	private boolean canConnect(IOFSwitch sw, MacAddress srcMac, MacAddress dstMac){
		Map<MacAddress, Integer> macToConnectionsMap = hostConnectionsMap.get(sw);

		// Source - number of active connections and connections limit 
		Integer srcConnectionsNumber = macToConnectionsMap.get(srcMac);
		Integer srcConnectionsLimit = hostMaxConnectionsMap.get(srcMac);		

		// Destination - number of active connections and connections limit 
		Integer dstConnectionsNumber = macToConnectionsMap.get(dstMac);
		Integer dstConnectionsLimit = hostMaxConnectionsMap.get(dstMac);		

		return srcConnectionsNumber < srcConnectionsLimit && dstConnectionsNumber < dstConnectionsLimit;
	}

	// Adds a new entry to the host connections map
	private void addToHostConnectionsMap(IOFSwitch sw, MacAddress srcMac){
		Map<MacAddress, Integer> hostConnectionsMapValue = hostConnectionsMap.computeIfAbsent(sw, k -> new HashMap<>());
		hostConnectionsMapValue.put(srcMac, hostConnectionsMapValue.getOrDefault(srcMac, 0) + 1);
	}

	// Updates the amount of active host connections on the map
	private void updateHostConnextionsMap(IOFSwitch sw, MacAddress srcMac){
			Map<MacAddress, Integer> hostConnectionsMapValue = hostConnectionsMap.get(sw);

			if (hostConnectionsMapValue != null && hostConnectionsMapValue.containsKey(srcMac)) {
				int connections = hostConnectionsMapValue.get(srcMac);
				
				if (connections > 1) {
					hostConnectionsMapValue.put(srcMac, connections - 1);
				} else {
					hostConnectionsMapValue.remove(srcMac); // No active connections left for this MAC - remove it from the hostConnectionsMap
				}
			}
	}



	// Install rule methods
	private void installDropRule(IOFSwitch sw, MacAddress srcMac, MacAddress dstMac) {
        Match match = sw.getOFFactory().buildMatch()
                .setExact(MatchField.ETH_SRC, srcMac)
                .setExact(MatchField.ETH_DST, dstMac)
                .build();

		List<OFAction> actions = Collections.emptyList();
		OFInstructions instructions = sw.getOFFactory().instructions();

        OFInstructionApplyActions applyActions = instructions.buildApplyActions()
			.setActions(actions) // Empty actions = drop
			.build();

        List<OFInstruction> instructionList = new ArrayList<>();
        instructionList.add(applyActions);

        // Install drop rule - NOTE: Higher priority than other rules
        boolean ruleCheck = SwitchCommands.installRule(sw, TableId.of(0), (short) (FLOWMOD_PRIORITY + 50), 
                                   match, instructionList, null, 
                                   FLOWMOD_DEFAULT_HARD_TIMEOUT, FLOWMOD_DEFAULT_IDLE_TIMEOUT, 
                                   OFBufferId.NO_BUFFER, false);

		
		if (ruleCheck){
			log.info("DROP RULE INSTALLED");
		}
    }

    private void installFlow(IOFSwitch sw, MacAddress srcMac, MacAddress dstMac, OFPort inPort, OFPort outPort) {
        Match match = sw.getOFFactory().buildMatch()
            .setExact(MatchField.IN_PORT, inPort)    
            .setExact(MatchField.ETH_SRC, srcMac)    
            .setExact(MatchField.ETH_DST, dstMac)    
            .build();

		// Creates action to forward packet
		OFActionOutput outputAction = sw.getOFFactory().actions().buildOutput()
			.setPort(outPort)                       // Sets the destination port to the outport 
			.setMaxLen(Integer.MAX_VALUE)           // Packet max value
			.build();

		List<OFAction> actions = new ArrayList<>();
		actions.add(outputAction);

		OFInstructionApplyActions applyActions = sw.getOFFactory().instructions().buildApplyActions()
			.setActions(actions)
			.build();

        List<OFInstruction> instructions = new ArrayList<>();
        instructions.add(applyActions);

        boolean ruleCheck = SwitchCommands.installRule(sw, TableId.of(0), (short) FLOWMOD_PRIORITY, 
                                   match, instructions, null,      
                                   FLOWMOD_DEFAULT_HARD_TIMEOUT, FLOWMOD_DEFAULT_IDLE_TIMEOUT,                        
                                   OFBufferId.NO_BUFFER, true);    
		
		if (ruleCheck){
			log.info("FLOW RULE (FORWARD) INSTALLED");
		}
    }

    private void installReverseFlow(IOFSwitch sw, MacAddress srcMac, MacAddress dstMac, OFPort inPort, OFPort outPort) {
        Match match = sw.getOFFactory().buildMatch()
            .setExact(MatchField.IN_PORT, outPort)    
            .setExact(MatchField.ETH_SRC, dstMac)    
            .setExact(MatchField.ETH_DST, srcMac)    
            .build();

		// Creates action to forward packet
		OFActionOutput outputAction = sw.getOFFactory().actions().buildOutput()
			.setPort(inPort)                       // Sets the destination port to the outport 
			.setMaxLen(Integer.MAX_VALUE)           // Packet max value
			.build();

		List<OFAction> actions = new ArrayList<>();
		actions.add(outputAction);

		OFInstructionApplyActions applyActions = sw.getOFFactory().instructions().buildApplyActions()
			.setActions(actions)
			.build();

        List<OFInstruction> instructions = new ArrayList<>();
        instructions.add(applyActions);

        boolean ruleCheck = SwitchCommands.installRule(sw, TableId.of(0), (short) FLOWMOD_PRIORITY, 
                                   match, instructions, null,      
                                   FLOWMOD_DEFAULT_HARD_TIMEOUT, FLOWMOD_DEFAULT_IDLE_TIMEOUT,                        
                                   OFBufferId.NO_BUFFER, true);    
		
		if (ruleCheck){
			log.info("FLOW REVERSE RULE (FORWARD) INSTALLED");
		}
    }

    private void installTcpFlowRule(IOFSwitch sw, IPv4Address srcIp, IPv4Address dstIp, TransportPort srcPort, TransportPort dstPort) {
		Match match = sw.getOFFactory().buildMatch()
				.setExact(MatchField.IPV4_SRC, srcIp)         // Match source IP
				.setExact(MatchField.IPV4_DST, dstIp)         // Match destination IP
				.setExact(MatchField.TCP_SRC, srcPort)        // Match TCP source port
				.setExact(MatchField.TCP_DST, dstPort)        // Match TCP destination port
				.build();
	
		OFActionOutput outputAction = sw.getOFFactory().actions().buildOutput()
				.setPort(OFPort.NORMAL)          // Forward to default path - triggers other rules 
				.setMaxLen(Integer.MAX_VALUE) 
				.build();
	
		List<OFAction> actions = new ArrayList<>();
		actions.add(outputAction);
	
		OFInstructionApplyActions applyActions = sw.getOFFactory().instructions().buildApplyActions()
				.setActions(actions)
				.build();

		List<OFInstruction> instructions = new ArrayList<>();
		instructions.add(applyActions);

		// Install the TCP flow rule 
		boolean ruleCheck = SwitchCommands.installRule(sw, TableId.of(0), (short) FLOWMOD_PRIORITY,
									match, instructions, null, 
									FLOWMOD_DEFAULT_HARD_TIMEOUT, FLOWMOD_DEFAULT_IDLE_TIMEOUT,
									OFBufferId.NO_BUFFER, true);
	
		if (ruleCheck){
			log.info("TCP flow rule installed");
		}
	}

    private void logFlowDetails(OFFlowRemoved flowRemovedMessage, IPv4Address srcIp, IPv4Address dstIp, TransportPort srcPort, TransportPort dstPort) {
		try {
			tcpFlowStatsWriter.write(String.format("%s,%s,%s,%s,%d,%d%n", 
												srcIp, dstIp, srcPort, dstPort, 
												flowRemovedMessage.getByteCount().getValue(), 
												flowRemovedMessage.getDurationSec()));
			tcpFlowStatsWriter.flush(); // Ensure the data is written immediately
		} catch (IOException e) {
			log.error("Failed to log TCP flow statistics", e);
		}

		log.info("TCP Flow Removed");
	}





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

	/*
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
		// Get input port and Ethernet payload
		OFPort inPort = (pi.getVersion().compareTo(OFVersion.OF_12) < 0) ? pi.getInPort() : pi.getMatch().get(MatchField.IN_PORT);
		Ethernet eth = IFloodlightProviderService.bcStore.get(cntx, IFloodlightProviderService.CONTEXT_PI_PAYLOAD);
	
		// Retrieve source and destination MAC addresses
		MacAddress srcMac = eth.getSourceMACAddress();
		MacAddress dstMac = eth.getDestinationMACAddress();
	
		// MAC-port learning
		addToPortMap(sw, srcMac, inPort);
		
		// Get the output port for the destination MAC
		OFPort outPort = getFromPortMap(sw, dstMac);
	
		// If destination port is unknown => broadcast/flood
		if (outPort == null) {
			log.info("Flooding packet as destination MAC {} is unknown on switch {}", dstMac, sw.getId());
			SwitchCommands.sendPacketOutPacketIn(sw, OFPort.FLOOD, pi);
			return Command.CONTINUE;
		}

		// Check connection limit for source IP
		if (isConnectionLimited(srcMac) && !canConnect(sw, srcMac, dstMac)) {
			installDropRule(sw, srcMac, dstMac); // Block new connections if limit exceeded
			return Command.STOP;
		}

		// Check if ethernet frame is IP
		if (eth.getEtherType() == EthType.IPv4) {
			IPv4 ipv4Packet = (IPv4) eth.getPayload();

			// Process TCP-specific flows
			if (ipv4Packet.getProtocol() == IpProtocol.TCP) {
				IPv4Address srcIp = ipv4Packet.getSourceAddress();
				IPv4Address dstIp = ipv4Packet.getDestinationAddress();

				TCP tcpPacket = (TCP) ipv4Packet.getPayload();
				installTcpFlowRule(sw, srcIp, dstIp, tcpPacket.getSourcePort(), tcpPacket.getDestinationPort());  // Install TCP flow rule
			}
		}
	
		// Forward packet to the proper destination
		if (!outPort.equals(inPort)) {
			log.info("Forwarding packet to port {} for destination MAC {}", outPort, dstMac);
			
			log.info("ADD TO HOST CONNECTIONS MAP");
			// Track new host-connection
			addToHostConnectionsMap(sw, srcMac);
			log.info("INSTALLING FLOW RULE");
			// Install forward flow
			installFlow(sw, srcMac, dstMac, inPort, outPort);  
			log.info("INSTALLING REVERSE FLOW RULE");
			// Install reverse flow for bidirectional communication
			installReverseFlow(sw, srcMac, dstMac, inPort, outPort);  
	
			// Forward the packet directly
			SwitchCommands.sendPacketOutPacketIn(sw, outPort, pi);
			return Command.STOP;
		}
	
		// Drop packets where the source and destination are on the same port
		log.warn("Dropping packet due to same input/output port for MAC {} on switch {}", dstMac, sw.getId());
		return Command.STOP;
	}
	

	/**
	 * Processes a flow removed message. 
	 * @param sw The switch that sent the flow removed message.
	 * @param flowRemovedMessage The flow removed message.
	 * @return Whether to continue processing this message or stop.
	 */
	private Command processFlowRemovedMessage(IOFSwitch sw, OFFlowRemoved flowRemovedMessage) {
		// Extract match fields from the flowRemovedMessage
		Match match = flowRemovedMessage.getMatch();
		IPv4Address srcIp = match.get(MatchField.IPV4_SRC);
		IPv4Address dstIp = match.get(MatchField.IPV4_DST);
		TransportPort srcPort = match.get(MatchField.TCP_SRC);
	    TransportPort dstPort = match.get(MatchField.TCP_DST);
		MacAddress srcMac = match.get(MatchField.ETH_SRC);
		MacAddress dstMac = match.get(MatchField.ETH_DST);
	
		// Log TCP-specific flow statistics if applicable
		if (srcIp != null && dstIp != null && match.isExact(MatchField.TCP_SRC)) {
			logFlowDetails(flowRemovedMessage, srcIp, dstIp, srcPort, dstPort);
		}
	
		// Update hostConnectionsMap to decrement connection count for the source MAC
		if (srcMac != null && hostConnectionsMap.containsKey(sw)) {
			updateHostConnectionsMap(sw, srcMac);
		}
	
		// Remove the MAC-to-Port mapping for the source MAC to revert to flooding
		if (srcMac != null) {
			removeFromPortMap(sw, srcMac);
		}
	
		// Clean up reverse flow if applicable
		if (srcMac != null && dstMac != null) {
			Match reverseMatch = sw.getOFFactory().buildMatch()
					.setExact(MatchField.ETH_SRC, dstMac)
					.setExact(MatchField.ETH_DST, srcMac)
					.build();
	
			SwitchCommands.removeRules(sw, TableId.of(0), reverseMatch);
			log.info("Removed reverse flow for srcMAC={}, dstMAC={}", dstMac, srcMac);
		}
	
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
	public Map<Class<? extends IFloodlightService>, IFloodlightService> getServiceImpls() { 
		return null; 
	}

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

		hostMaxConnectionsMap = new ConcurrentHashMap<MacAddress, Integer>();
		hostConnectionsMap = new ConcurrentHashMap<IOFSwitch, Map<MacAddress, Integer>>();
		
		try {
            tcpFlowStatsWriter = new FileWriter("/home/pfa/Desktop/tcp_flow_stats.csv");
            tcpFlowStatsWriter.write("SourceIP, DestinationIP, SourcePort, DestinationPort, ByteCount, Duration\n");

        } catch (IOException e) {
            log.error("Failed to open TCP flow statistics file", e);
        }

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

