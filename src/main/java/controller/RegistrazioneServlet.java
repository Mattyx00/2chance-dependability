package controller;

import model.beans.Utente;
import services.RegistrazioneService;


import javax.servlet.RequestDispatcher;
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
import java.util.ArrayList;

@WebServlet(name = "RegistrazioneServlet", urlPatterns = "/RegistrazioneServlet/*")
@MultipartConfig
public class RegistrazioneServlet extends HttpServlet {
    private RegistrazioneService registrazioneService;

    @Override
    public void init() throws ServletException {
        try {
            this.registrazioneService = new RegistrazioneService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize RegistrazioneService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            String nome = request.getParameter("nome");
            String cognome = request.getParameter("cognome");
            String password = request.getParameter("password");
            String email = request.getParameter("email");
            String telefono = request.getParameter("telefono");

            //prendo file dalla richiesta
            Part part = request.getPart("file");
            String fileName = Paths.get(part.getSubmittedFileName()).getFileName().toString();

            File file;
            try (InputStream fileStream = part.getInputStream()) {
                String currentDirectory = System.getProperty("user.dir");
                Path currentPath = Paths.get(currentDirectory);
                Path parentPath = currentPath.getParent(); // Ottiene il percorso del genitore
                Path uploadPath = parentPath.resolve("upload"); // Risolve "upload" nel percorso del genitore

                String uploadRoot = uploadPath.toString() + File.separator;
                file = new File(uploadRoot + fileName);
                if (!file.exists())         //salvo il file all'interno della cartella upload
                    Files.copy(fileStream, file.toPath());
            }

            ArrayList<String> errori = registrazioneService.validateAndRegister(nome, cognome, password, email, telefono, fileName);

            if (!errori.isEmpty()) {
                Utente u = new Utente();
                u.setNome(nome);
                u.setCognome(cognome);
                u.setPassword(password);
                u.setEmail(email);
                u.setTelefono(telefono);
                u.setImmagine(fileName);
                
                request.setAttribute("utente", u);
                request.setAttribute("errori", errori);
                String address = "/registrazione.jsp";
                RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                dispatcher.forward(request, response);
            } else {
                Utente u = registrazioneService.getUserByEmailPassword(email, password);
                request.setAttribute("utente", u);
                request.setAttribute("errori", errori);
                request.getSession().setAttribute("user", u);
                response.sendRedirect(request.getServletContext().getContextPath() + "/landingpage");
            }

        } catch (SQLException throwable) {
            throwable.printStackTrace();
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
