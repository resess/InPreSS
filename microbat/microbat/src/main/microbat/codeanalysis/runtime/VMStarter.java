package microbat.codeanalysis.runtime;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import org.eclipse.jdi.internal.VirtualMachineManagerImpl;

import com.sun.jdi.VirtualMachine;
import com.sun.jdi.VirtualMachineManager;
import com.sun.jdi.connect.Connector;
import com.sun.jdi.connect.IllegalConnectorArgumentsException;
import com.sun.jdi.connect.LaunchingConnector;
import com.sun.jdi.connect.VMStartException;

import sav.strategies.dto.AppJavaClassPath;
import sav.strategies.vm.BootstrapPlugin;


@SuppressWarnings("restriction")
public class VMStarter {
	
	private AppJavaClassPath configuration;
	private boolean isRunOnTestCaseMode = false;
	
	public VMStarter(AppJavaClassPath classPath, boolean isRunOnTestCaseMode){
		this.configuration = classPath;
		this.isRunOnTestCaseMode = isRunOnTestCaseMode;
	}
	
	public VirtualMachine start(){
		VirtualMachine vm = null;
		
		VirtualMachineManager manager = BootstrapPlugin.virtualMachineManager();
		
//		LaunchingConnector connector = getCommandLineConnector();
		SocketLanchingConnector0 connector = new SocketLanchingConnector0((VirtualMachineManagerImpl)manager);
		Map<String, Connector.Argument> arguments = connectorArguments(connector, configuration);
		
		System.currentTimeMillis();
		
        try {
        	File workDir = new File(configuration.getWorkingDirectory());
        	vm = connector.launch(arguments, workDir, configuration);
        	return vm;
        } catch (IOException exc) {
            throw new Error("Unable to launch target VM: " + exc);
        } catch (IllegalConnectorArgumentsException exc) {
            throw new Error("Internal error: " + exc);
        } catch (VMStartException exc) {
            throw new Error("Target VM failed to initialize: " +
                            exc.getMessage());
        }
        
        
	}
	
	protected LaunchingConnector getCommandLineConnector() {
		List<Connector> conns = BootstrapPlugin.virtualMachineManager().allConnectors();
		for (Connector conn : conns) {
			if (conn.name().equals("com.sun.jdi.CommandLineLaunch")){
				return (LaunchingConnector) conn;				
			}
		}
		throw new Error("No launching connector found");
	}
	
	/**
     * Return the launching connector's arguments.
     */
    private Map<String, Connector.Argument> connectorArguments(LaunchingConnector connector, 
    		AppJavaClassPath configuration) {
        Map<String, Connector.Argument> arguments = connector.defaultArguments();
        
        Connector.Argument argument = arguments.get("home");
        argument.setValue(configuration.getJavaHome());
        
        Connector.Argument mainArg = (Connector.Argument)arguments.get("main");
        if (mainArg == null) {
            throw new Error("Bad launching connector");
        }
        
        String mainValue;
        if(isRunOnTestCaseMode && configuration.getOptionalTestClass() != null && configuration.getOptionalTestMethod() != null){
        	mainValue = configuration.getLaunchClass() + " " + configuration.getOptionalTestClass() 
        			+ " " + configuration.getOptionalTestMethod();
        }
        else{
        	mainValue = configuration.getLaunchClass();
        }
        mainArg.setValue(mainValue);
        
        // We need a VM that supports watchpoints
        Connector.Argument optionArg =
            (Connector.Argument)arguments.get("options");

        
        if (optionArg == null) {
            throw new Error("Bad launching connector");
        }
        
        
        String classPathString = "";
        for(String classPath: configuration.getClasspaths()){
        	classPathString += classPath + File.pathSeparator;
        }
       
        if(classPathString.length() != 0){
        	classPathString = classPathString.substring(0, classPathString.length()-1);
        	classPathString = "-cp " + classPathString;
        }
        optionArg.setValue(classPathString);
        
//      optionArg.setValue("-cp \"F:\\workspace\\runtime-debugging\\Memo\\bin\"");
        
        return arguments;
    }
}
