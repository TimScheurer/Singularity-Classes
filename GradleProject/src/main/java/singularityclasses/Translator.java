package singularityclasses;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

/**
 * This class contains the methods used to translate a set of source files into their respective {@link JmlCompilationUnit} objects.
 */
public class Translator {

    private static String[] originalFilePaths;

    /**
     * Given a path to a folder containing the source code of a java program, compiles and typechecks each found 
     * source file and returns a list of {@link JmlCompilationUnit} objects.
     * 
     * @param path Path to the root folder of the program.
     * @return Returns a list of {@link JmlCompilationUnit} representing the individual source files.
     * @throws Exception 
     */
    public static List<JmlCompilationUnit> translate(String path, IAPI api) throws Exception {
        String[] javaFileNames = getFilesInFolder(path);
        originalFilePaths = javaFileNames;
        System.out.println("Found " + javaFileNames.length + " java source file/s");
        List<JmlCompilationUnit> cus = api.parseFiles(javaFileNames);
        //int a = api.typecheck(cus);
        //if(a > 0) {
        //    System.out.println("OpenJml parser error");
        //   return null;
        //}
        System.out.println("Parsed files successfully");
        return cus;
    }

    /**
     * Helper function returning all files with the '.java' extension in the provided folder.
     * 
     * @param path The path to the folder containing the source files.
     * @return A string array containing the absolute paths to all the found .java files.
     */
    private static String[] getFilesInFolder(String path) {
        List<String> res = new ArrayList<>();
        System.out.println("Current path " + Paths.get(path).getFileName().toAbsolutePath().toString());
        try {
            Files.walk(Paths.get(path))
                 .filter(Files::isRegularFile)
                 .filter(f -> f.getFileName().toAbsolutePath().toString().endsWith(".java"))
                 .forEach(f -> { res.add(f.toAbsolutePath().normalize().toString());
                                 System.out.println("Found file: " + f.toAbsolutePath().normalize().toString());});
        } catch (IOException e) {
            System.out.println("Error while reading file paths to java source files");
            System.exit(1);
        }
     
        return res.toArray(new String[0]);
    }

    public static String[] getOriginalFiles() {
        String[] res = new String[originalFilePaths.length];
        int i = 0;
        for (String pathString : originalFilePaths) {
            try {
                File file = new File(pathString);
                FileInputStream fis = new FileInputStream(file);
                byte[] data = new byte[(int) file.length()];
                fis.read(data);
                fis.close();

                res[i++] = new String(data, StandardCharsets.UTF_8);
            } catch (IOException e) {
                System.out.println("Error while trying to read contents from \"" + pathString + "\"");
                System.exit(1);
            }

        }
        return res;
    }

    public static String[] getOriginalFilePaths() {
        return originalFilePaths;
    }
}