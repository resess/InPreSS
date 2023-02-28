package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.io.FileUtils;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import tregression.empiricalstudy.Defects4jProjectConfig;
import tregression.empiricalstudy.TestCase;

public class projConfig extends Defects4jProjectConfig{
	public String srcTestFolder;
	public String srcSourceFolder;
	public String bytecodeTestFolder;
	public String bytecodeSourceFolder;
	public String buildFolder;
	
	public List<String> additionalSourceFolder = new ArrayList<>();
	
	public String projectName;
	public int bugID;
	public String configFile;
	
	public String rootPath = ""+File.separator+"home"+File.separator+"linyun"+File.separator+"doc"+File.separator+"git_space"+File.separator+"defects4j"+File.separator+"framework"+File.separator+"bin"+File.separator+"defects4j";
	//public String javaHome = Activator.getDefault().getPreferenceStore().getString(MicrobatPreference.JAVA7HOME_PATH);
	public String javaHome = System.getProperty("java.home");
	private projConfig(String srcTestFolder, String srcSourceFolder, String bytecodeTestFolder,
			String bytecodeSourceFolder, String buildFolder, String projectName, int bugID) {
		super(srcTestFolder,srcSourceFolder,bytecodeTestFolder,bytecodeSourceFolder,buildFolder,projectName,bugID);
		this.configFile = "E";
	}
	public static projConfig getConfig(String baseProjPath, String projectName, int bugID, String ereasOrSlicer) throws IOException, InterruptedException {
		projConfig config = null;
	    String proPath = baseProjPath + projectName + "/" + bugID;
		String buggyPath = proPath + "/bug/";
		String fixPath = proPath + "/fix/";
		////////////////////////////////////////////////////////////////
		if (projectName.equals("InPreSS")) {
			if(bugID==1){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "E";
			}
			else if(bugID==2){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
			else if(bugID==3){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
			else if(bugID==4){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
			else if(bugID==5){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "E";
			}
			else if(bugID==6){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";			
			}
			else if(bugID==7){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
			else if(bugID==8){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
			else if(bugID==9){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = "S";
			}
		}
		if (projectName.equals("Toy")) {
			if(bugID<21){
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);		
			}			
		}
		////////////////////////////////////////////////////////////////
		
		else if(projectName.equals("Chart")) {
            Path newPath = Paths.get(buggyPath+"build");
            Path oldPath = Paths.get(fixPath+"build");
            Path newPathT = Paths.get(buggyPath+"build-tests");
            Path oldPathT = Paths.get(fixPath+"build-tests");
			if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
				saveBugAndTerminate(baseProjPath,projectName, bugID);
				System.exit(0);
			}	
			config = new projConfig("tests", "source", "build-tests", "build", "build", projectName, bugID);
			config.configFile = ereasOrSlicer;
			if(config.configFile.contentEquals("S"))
				getSlice(baseProjPath, "build-tests", "build", projectName, bugID,"lib");
		}
		
		else if (projectName.equals("Closure")) {
            Path newPath = Paths.get(buggyPath+"build");
            Path oldPath = Paths.get(fixPath+"build");
			if(!Files.exists(newPath) || !Files.exists(oldPath)) {
				saveBugAndTerminate(baseProjPath,projectName, bugID);
				System.exit(0);
			}			
			config = new projConfig("test", "src", "build"+File.separator+"test", "build"+File.separator+"classes", "build", projectName, bugID);
			config.configFile = ereasOrSlicer;
			
            Path path = Paths.get(buggyPath + "build/lib")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "build/lib");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}			
				source = new File(fixPath + "build/lib");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			if(config.configFile.contentEquals("S"))
				getSlice(baseProjPath, "build"+File.separator+"test","build"+File.separator+"classes", projectName, bugID,"lib");
		}
			
		else if (projectName.equals("Lang")) {
			if(bugID<21){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"tests");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}	
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"tests", "target"+File.separator+"classes", "target", projectName, bugID);		
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			   
			}
			else if(bugID>=36 && bugID<=41){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else if(bugID<42){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"tests");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"tests", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"tests","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			
//			if(bugID>=36 && bugID<=41){
//				config.srcSourceFolder = "src"+File.separator+"java";
//				config.srcTestFolder = "src"+File.separator+"test";
//			}
		}
		
		else if (projectName.equals("Math")) {
			if(bugID<85){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);	
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test", "src"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
		}
		else if (projectName.equals("Mockito")) {
			Path path = Paths.get(buggyPath + "build/lib")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "build/lib");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "build/lib");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/build")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/build");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/build");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/repackaged")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/repackaged");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/repackaged");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/sources")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/sources");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/sources");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
		    path = Paths.get(buggyPath + "lib/test")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/test");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/test");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/compile")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/compile");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/compile");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			path = Paths.get(buggyPath + "lib/run")	;	
			if(Files.exists(path)) {
				File source = new File(buggyPath + "lib/run");
				File dest = new File(buggyPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
				source = new File(fixPath + "lib/run");
				dest = new File(fixPath + "lib");
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
			}
			if(bugID<12 || bugID==20 || bugID==21 || bugID==18 || bugID==19){
				Path newPath = Paths.get(buggyPath+"build"+File.separator+"classes"+File.separator+"main");
	            Path oldPath = Paths.get(fixPath+"build"+File.separator+"classes"+File.separator+"main");
	            Path newPathT = Paths.get(buggyPath+"build"+File.separator+"classes"+File.separator+"test");
	            Path oldPathT = Paths.get(fixPath+"build"+File.separator+"classes"+File.separator+"test");
				if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				
				config = new projConfig("test", "src", "build"+File.separator+"classes"+File.separator+"test", "build"+File.separator+"classes"+File.separator+"main", "build", projectName, bugID);	
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath, "build"+File.separator+"classes"+File.separator+"test","build"+File.separator+"classes"+File.separator+"main", projectName, bugID,"lib");
			}
			else{
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
	            if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("test", "src", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"lib");
			}
			
			List<String> addSrcList = new ArrayList<>();
			addSrcList.add("mockmaker" + File.separator + "bytebuddy"+ File.separator + "main" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "bytebuddy"+ File.separator + "test" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "cglib"+ File.separator + "main" + File.separator + "java");
			addSrcList.add("mockmaker" + File.separator + "cglib"+ File.separator + "test" + File.separator + "java");
			config.additionalSourceFolder = addSrcList;
		}
		else if (projectName.equals("Time")) {
			if(bugID<12){
				Path newPath = Paths.get(buggyPath+"target"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"target"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"target"+File.separator+"test-classes");
	            Path oldPathT = Paths.get(fixPath+"target"+File.separator+"test-classes");
	            if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "target"+File.separator+"test-classes", "target"+File.separator+"classes", "target", projectName, bugID);				
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "target"+File.separator+"test-classes","target"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
			else{
				Path newPath = Paths.get(buggyPath+"build"+File.separator+"classes");
	            Path oldPath = Paths.get(fixPath+"build"+File.separator+"classes");
	            Path newPathT = Paths.get(buggyPath+"build"+File.separator+"tests");
	            Path oldPathT = Paths.get(fixPath+"build"+File.separator+"tests");
	            if(!Files.exists(newPath) || !Files.exists(oldPath) || !Files.exists(newPathT) || !Files.exists(oldPathT)) {
					saveBugAndTerminate(baseProjPath,projectName, bugID);
					System.exit(0);
				}
				config = new projConfig("src"+File.separator+"test"+File.separator+"java", "src"+File.separator+"main"+File.separator+"java", "build"+File.separator+"tests", "build"+File.separator+"classes", "build", projectName, bugID);
				config.configFile = ereasOrSlicer;
				if(config.configFile.contentEquals("S"))
					getSlice(baseProjPath,  "build"+File.separator+"tests","build"+File.separator+"classes", projectName, bugID,"target"+File.separator+"dependency");
			}
		}
		
		return config;
	}
private static void saveBugAndTerminate(String baseProjPath, String projectName2, int bugID2) {
	String results = baseProjPath+"/results/"+projectName2+"NoBuild.xlsx";
    File tempFile = new File(results);
    boolean FirstTime = false;
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######
    /////////////////#######////#######////#######////#######////#######////#######	
	if (!tempFile.exists()) {
        FirstTime=true;
        XSSFWorkbook workbook = new XSSFWorkbook();
        XSSFSheet sheet = workbook.createSheet("stats");
        try {
        	FileOutputStream outputStream = new FileOutputStream(results);
            workbook.write(outputStream);
            workbook.close();
        	outputStream.close();
        } catch (Exception e) {
        }
    }		

    if (FirstTime) {		    	
        String[] header = {"Bug ID"};
        WriteToExcel(results, header, "stats",false, true);
    }
    String[] data = {String.valueOf(bugID2)};
    WriteToExcel(results,data,"stats",false, false);	
		
	}
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
public static void WriteToExcel(String ExcelFilePath, String[] RowData, String sheetName,boolean existing,boolean firstTime){
    try {
  
    	    FileInputStream myxls = new FileInputStream(ExcelFilePath);
            XSSFWorkbook ExcelWorkbook = new XSSFWorkbook(myxls);
            XSSFSheet worksheet;
   
            if (existing) {
            	if (firstTime)
            		worksheet = ExcelWorkbook.createSheet(sheetName);
            	else 
            		worksheet = ExcelWorkbook.getSheet(sheetName);	            		            	
            }
            else {
//            XSSFSheet worksheet = ExcelWorkbook.getSheetAt(id);
            	 worksheet = ExcelWorkbook.getSheet(sheetName);
            }
            int lastRow=worksheet.getLastRowNum();          
            if(!firstTime)
            	lastRow++;
            Row row = worksheet.createRow(lastRow);
            for (int index = 0; index < RowData.length; index++) {
                row.createCell(index).setCellValue(RowData[index]);
            }
            
            myxls.close();

            try {
            	FileOutputStream output_file =new FileOutputStream(new File(ExcelFilePath));
                ExcelWorkbook.write(output_file);
                output_file.close();
                ExcelWorkbook.close();
            }
            catch(Exception e){}
    }
    catch(Exception e){
    }
}
	////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
	private static void getSlice(String baseProj, String testFolder, String classFolder, String projectName, int bugID, String depPath) throws IOException, InterruptedException {
			
//	        String slicerPath = System.getProperty("user.dir")+"/deps/Slicer4J/scripts/slicer4j.py";
		    String slicerPath = "/Users/sahar1/Documents/Projects/LibraryUpadate/Code/Tools/Slicer4J/scripts/slicer4j.py";
//		    String slicerPath = "/Users/sahar1/Documents/Github/InPreSS/InPreSS/deps/Slicer4J/scripts/slicer4j.py";
			
//		    String slicerPath = "/data/shrbadihi/projects/client_library/libre/Jars/deps/Slicer4J/scripts/slicer4j.py";//thanos
        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
		    String proPath = baseProj + projectName + "/" + bugID;
			String buggyPath = proPath + "/bug/";
			String fixPath = proPath + "/fix/";
			Path path = Paths.get(proPath+"/results");		
			if(!Files.exists(path)) {
				new File(proPath+"/results").mkdirs();
				new File(proPath+"/results/new").mkdirs();
				new File(proPath+"/results/old").mkdirs();				

			}
			new File(proPath+"/results/old/Slicer4JResults").mkdirs();
			new File(proPath+"/results/new/Slicer4JResults").mkdirs();
			
	        String failingFile = buggyPath  + "failing_tests";
			File file = new File(failingFile);
			BufferedReader reader = new BufferedReader(new FileReader(file));
			String testClass = "";
			String testMethod = "";
			String sliceLine = "";				
			String line = null;
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("---")) {
					 testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
					 testMethod = line.substring(line.indexOf("::") + 2, line.length());				
				}
				else {
					if (line.contains(testClass) && line.contains(testMethod)) {
						String temp = (line.split(":")[1]);
//						System.out.println(temp);
//						if (temp.contains(")"))
//							System.out.println(temp.indexOf(")"));
						sliceLine = temp.substring(0, temp.indexOf(")"));
//						System.out.println(sliceLine);
						break;
					}						    
				}					
			}
			reader.close();
	        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
//		    Path Slicer4JResultsPath = Paths.get(proPath+"/results/new/Slicer4JResults");
	        Path instrumentedJar = Paths.get(proPath+"/results/new/Slicer4JResults/program_i.jar");
			if(!Files.exists(instrumentedJar)) {
				//1. copy the test classes
				File source = new File(buggyPath + testFolder);
				File dest = new File(buggyPath + classFolder);
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
//		        String cmd = "cp -R " + buggyPath + testFolder + "/* " + buggyPath + classFolder + "/";	  
//		        System.out.println(cmd);
//				Process p1 = Runtime.getRuntime().exec(cmd);
//				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
//				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
//				String line1 = null;
//				String answer = in.readLine();
//				if(answer == null){
//					String error = err.readLine();
//					if (error != null)
//						System.out.println(error);
//				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}	
//				in.close();
//				err.close();
//				p1.waitFor();
  
//				//2. create a jar 
				String cmd = "jar cvf " + proPath + "/results/new/program.jar" + " -C " + buggyPath + classFolder + " .";
				Process p1 = Runtime.getRuntime().exec(cmd);
				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
				String line1 = null;
				String answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}				
				in.close();
				err.close();
				int c = p1.waitFor();
//				System.out.println("Process exitValue: " + c);
				System.out.println("Finish creating jar");
	        
//		        //3. slice 
		        cmd = "python3 " + slicerPath +" -j " + proPath + "/results/new/program.jar" + " -o " + proPath + "/results/new/Slicer4JResults"+" -b " + testClass + ":" + sliceLine + " -tc " + testClass + " -tm " + testMethod + " -dep " + buggyPath + depPath;
		        System.out.println(cmd);
       
	            String[] commads = {"python3", slicerPath, "-j", proPath + "/results/new/program.jar","-o",proPath + "/results/new/Slicer4JResults","-b",testClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", buggyPath + depPath};
				
	            Process p = new ProcessBuilder(commads)
	                    .redirectErrorStream(true)
	                    .start();
				in = new BufferedReader(new InputStreamReader(p.getInputStream()));
				err = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				line1 = null;
				answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line1 = in.readLine()) != null) {
						System.out.println(line1);
					}				
				in.close();
				err.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish creating slice");
//		        
			}
	        /////////// /////////// /////////// /////////// /////////// /////////// ///////////
			/////////// /////////// /////////// /////////// /////////// /////////// ///////////
	        instrumentedJar = Paths.get(proPath+"/results/old/Slicer4JResults/program_i.jar");
			if(!Files.exists(instrumentedJar)) {
				//1. copy the test classes
				File source = new File(fixPath + testFolder);
				File dest = new File(fixPath + classFolder);
				try {
				    FileUtils.copyDirectory(source, dest);
				} catch (IOException e) {
				    e.printStackTrace();
				}
//		         cmd = "cp -R " + fixPath + testFolder + "/* " + fixPath + classFolder + "/";	        
//				 p1 = Runtime.getRuntime().exec(cmd);
//				 in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
//				 err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
//				 line1 = null;
//				 answer = in.readLine();
//				if(answer == null){
//					String error = err.readLine();
//					if (error != null)
//						System.out.println(error);
//				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}				
//				in.close();
//				err.close();
//				p1.waitFor();
  
//				//2. create a jar 
				String cmd = "jar cvf " + proPath + "/results/old/program.jar" + " -C " + fixPath + classFolder + " .";
				Process p1 = Runtime.getRuntime().exec(cmd);
				BufferedReader in = new BufferedReader(new InputStreamReader(p1.getInputStream()));
				BufferedReader err = new BufferedReader(new InputStreamReader(p1.getErrorStream()));
				String line1 = null;
				String answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
//				else 
//					while ((line1 = in.readLine()) != null) {
//						System.out.println(line1);
//					}				
				in.close();
				err.close();
				int c = p1.waitFor();
//				System.out.println("Process exitValue: " + c);
				System.out.println("Finish creating jar");
	        
//		        //3. slice 
				cmd = "python3 " + slicerPath +" -j " + proPath + "/results/old/program.jar" + " -o " + proPath + "/results/old/Slicer4JResults"+" -b " + testClass + ":" + sliceLine + " -tc " + testClass + " -tm " + testMethod + " -dep " + buggyPath + depPath;
			        System.out.println(cmd);
	            String[] commads2 = {"python3", slicerPath, "-j", proPath + "/results/old/program.jar","-o",proPath + "/results/old/Slicer4JResults","-b",testClass + ":" + sliceLine,"-tc",testClass,"-tm",testMethod,"-dep", fixPath + depPath};
				
	            Process p = new ProcessBuilder(commads2)
	                    .redirectErrorStream(true)
	                    .start();
				in = new BufferedReader(new InputStreamReader(p.getInputStream()));
				err = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				line1 = null;
				answer = in.readLine();
				if(answer == null){
					String error = err.readLine();
					if (error != null)
						System.out.println(error);
				}
				else 
					while ((line1 = in.readLine()) != null) {
						System.out.println(line1);
					}				
				in.close();
				err.close();
				int rc = p.waitFor();
//				System.out.println("Process exitValue: " + rc);
				System.out.println("Finish creating slice");
			}		
	}
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
	public static List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		String failingFile = buggyVersionPath + File.separator + "failing_tests";
		File file = new File(failingFile);

		BufferedReader reader = new BufferedReader(new FileReader(file));

		List<TestCase> list = new ArrayList<>();
		String line = null;
		while ((line = reader.readLine()) != null) {
			if (line.startsWith("---")) {
				String testClass = line.substring(line.indexOf(" ") + 1, line.indexOf("::"));
				String testMethod = line.substring(line.indexOf("::") + 2, line.length());

				TestCase tc = new TestCase(testClass, testMethod);
				list.add(tc);
			}
		}
		reader.close();

		return list;
	}

}
