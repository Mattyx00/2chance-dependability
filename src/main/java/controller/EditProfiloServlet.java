package controller;

import model.beans.Utente;
import model.dao.UtenteDAO;

import javax.servlet.ServletException;
import javax.servlet.annotation.MultipartConfig;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.Part;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;
@MultipartConfig
@WebServlet(name = "EditProfiloServlet", urlPatterns = "/EditProfiloServlet/*")
public class EditProfiloServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String path = request.getPathInfo() == null ? "/" : request.getPathInfo();

        if(path.equals("/editImmagine")){
            try {
                UtenteDAO dao = new UtenteDAO();
                Utente u = (Utente) request.getSession().getAttribute("user");
                int idProfilo = u.getId();
                Part part = request.getPart("modifica");
                String fileName = Paths.get(part.getSubmittedFileName()).getFileName().toString(); //nome immagine
                dao.editProfilo(path, fileName, idProfilo);

                File file;
                try (InputStream fileStream = part.getInputStream()) { //ottengo il path corrente e salvo l'immagine in upload
                    String currentDirectory = System.getProperty("user.dir");
                    Path currentPath = Paths.get(currentDirectory);
                    Path parentPath = currentPath.getParent(); // Ottiene il percorso del genitore
                    System.out.println(parentPath);
                    Path uploadPath = parentPath.resolve("upload"); // Risolve "upload" nel percorso del genitore

                    String uploadRoot = uploadPath.toString() + File.separator;
                    file = new File(uploadRoot + fileName);
                    if (!file.exists())
                        Files.copy(fileStream, file.toPath());
                }
                u = dao.getUtenteById(idProfilo);
                request.getSession().setAttribute("user", u);
                response.sendRedirect( request.getServletContext().getContextPath()+"/paginaUtente.jsp");

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }


        }

        else try {
            UtenteDAO dao = new UtenteDAO();
            String modifica = request.getParameter("modifica"); //modifica sul db
            Utente u = ((Utente) request.getSession().getAttribute("user"));
            int idProfilo = u.getId();
            dao.editProfilo(path, modifica, idProfilo);
            u = dao.getUtenteById(idProfilo);
            request.getSession().setAttribute("user", u);
            response.sendRedirect( request.getServletContext().getContextPath()+"/paginaUtente.jsp");
        } catch (SQLException throwables) {
            throwables.printStackTrace();
        }

    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        doGet(req, resp);
    }
}