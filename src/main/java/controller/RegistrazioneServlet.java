package controller;

import model.beans.Utente;
import model.dao.UtenteDAO;

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
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            UtenteDAO dao = new UtenteDAO();
            ArrayList errori = new ArrayList();
            Utente u = new Utente();
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

            String emailRegex = "^[\\w-\\.]+@([\\w-]+\\.)+[\\w-]{2,4}$";
            String onlyTextRegex = "^[a-zA-Z]*$"; //solo testo
            String telRegex = "^\\d{10}$"; //almeno 10 caratteri
            String passwordRegex = "^(?=.*[A-Z]).{8,}$"; //almeno 8 caratteri ed una maiuscola
            if(nome == null || nome.equals("") || !nome.matches(onlyTextRegex)){
                errori.add("Errore nome, riprovare");
            }

            else if(cognome == null || cognome.equals("") || !cognome.matches(onlyTextRegex)){
                errori.add("Errore cognome, riprovare");
            }

            else if(password == null || password.equals("") || !password.matches(passwordRegex)){
                errori.add("Errore password, riprovare");
            }

            else if(email == null || email.equals("") || !email.matches(emailRegex)){
                errori.add("Errore email, riprovare");
            }

            else if(UtenteDAO.isEmailPresent(email)){
                errori.add("Email già in utilizzo");
            }

            else if(telefono == null || telefono.equals("") || !telefono.matches(telRegex)){
                errori.add("Errore telefono, riprovare");
            }

            if(u == null){
                throw new NullPointerException("Internal error");
            }
            else{
                u.setNome(nome);
                u.setCognome(cognome);
                u.setPassword(password);
                u.setEmail(email);
                u.setTelefono(telefono);
                u.setImmagine(fileName);


                if(errori.size()>0){
                    request.setAttribute("utente", u);
                    request.setAttribute("errori", errori);
                    String address = "/registrazione.jsp";
                    RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                    dispatcher.forward(request, response);
                }else{
                    dao.addUtente(u); //salvo l'utente nel database
                    u = dao.getUserByEmailPassword(email, password);
                    request.setAttribute("utente", u);
                    request.setAttribute("errori", errori);
                    request.getSession().setAttribute("user", u);
                    response.sendRedirect(request.getServletContext().getContextPath() + "/landingpage");
                }
            }
        } catch (SQLException throwable) {
            throwable.printStackTrace();
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
