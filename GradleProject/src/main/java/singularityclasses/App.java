package singularityclasses;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

public class App {
    
    public static void main(String[] args) {
        if (args.length == 0) {
            System.out.println("Provide the path to an annotated java program.");
            return;
        }

        System.out.println("Selected folder: " + args[0]);
        List<JmlCompilationUnit> cus;
        IAPI api;
        Context context;
        JmlTree.Maker maker;

        try {
            api = Factory.makeAPI();
            cus = Translator.translate(args[0], api);
            context = api.context();
            maker = JmlTree.Maker.instance(context);

            if (cus == null) {
                System.out.println("Failed to retrieve compilation units");
                System.exit(1);
            }

            Scanner scanner = new Scanner(JmlTreeScanner.AST_JML_MODE, context);

            for (JmlCompilationUnit cu : cus) {
                scanner.setCurrentCompilationUnit(cu);
                scanner.scan(cu);
            }

            String[] originalFileContents = Translator.getOriginalFiles();
            String[] originalFilePaths = Translator.getOriginalFilePaths();
            String[] originalFileNames = Util.getNames(cus);

            List<JmlTree.JmlCompilationUnit> validInterfaces = scanner.getFoundValidInterfaces();

            String[][] translations = CodeTransformer.translate(originalFileContents, originalFileNames, originalFilePaths, Util.getNames(validInterfaces));
            print(translations[0], translations[1]);
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static void print(String[] contents, String[] paths) {
        if (contents.length != paths.length) return;
        try {
            for (int i = 0; i < contents.length; i++) {
                String newName = paths[i].replace(".java", "2.java");
                FileWriter writer = new FileWriter(newName);
                writer.write(contents[i]);
                writer.flush();
                writer.close();
                System.out.println("Wrote file " + newName);
            }
        } catch (IOException e) {
            System.out.println("Failed writing file");
            System.exit(1);
        }
    }
}
