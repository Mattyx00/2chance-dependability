package services;

import model.beans.Utente;
import model.dao.UtenteDAO;

import javax.servlet.http.Part;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;

public class EditProfiloService {
    private UtenteDAO utenteDAO;

    public EditProfiloService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public EditProfiloService(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }

    public Utente editImmagine(Utente u, Part part, String path) throws SQLException, IOException {
        int idProfilo = u.getId();
        String fileName = Paths.get(part.getSubmittedFileName()).getFileName().toString(); //nome immagine
        utenteDAO.editProfilo(path, fileName, idProfilo);

        File file;
        try (InputStream fileStream = part.getInputStream()) { //ottengo il path corrente e salvo l'immagine in upload
            String currentDirectory = System.getProperty("user.dir");
            Path currentPath = Paths.get(currentDirectory);
            Path parentPath = currentPath.getParent(); // Ottiene il percorso del genitore
            Path uploadPath = parentPath.resolve("upload"); // Risolve "upload" nel percorso del genitore

            // Ensure directory exists
            if (!Files.exists(uploadPath)) {
                Files.createDirectories(uploadPath);
            }

            String uploadRoot = uploadPath.toString() + File.separator;
            file = new File(uploadRoot + fileName);
            if (!file.exists())
                Files.copy(fileStream, file.toPath());
        }
        return utenteDAO.getUtenteById(idProfilo);
    }

    public Utente editProfilo(Utente u, String modifica, String path) throws SQLException {
        int idProfilo = u.getId();
        utenteDAO.editProfilo(path, modifica, idProfilo);
        return utenteDAO.getUtenteById(idProfilo);
    }
}
