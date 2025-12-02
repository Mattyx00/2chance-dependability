package services;

import model.beans.Utente;
import model.dao.UtenteDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class RegistrazioneService {
    private UtenteDAO utenteDAO;

    public RegistrazioneService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public RegistrazioneService(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }

    public ArrayList<String> validateAndRegister(String nome, String cognome, String password, String email, String telefono, String fileName) throws SQLException {
        ArrayList<String> errori = new ArrayList<>();
        String emailRegex = "^[\\w-\\.]+@([\\w-]+\\.)+[\\w-]{2,4}$";
        String onlyTextRegex = "^[a-zA-Z]*$"; //solo testo
        String telRegex = "^\\d{10}$"; //almeno 10 caratteri
        String passwordRegex = "^(?=.*[A-Z]).{8,}$"; //almeno 8 caratteri ed una maiuscola

        if (nome == null || nome.equals("") || !nome.matches(onlyTextRegex)) {
            errori.add("Errore nome, riprovare");
        } else if (cognome == null || cognome.equals("") || !cognome.matches(onlyTextRegex)) {
            errori.add("Errore cognome, riprovare");
        } else if (password == null || password.equals("") || !password.matches(passwordRegex)) {
            errori.add("Errore password, riprovare");
        } else if (email == null || email.equals("") || !email.matches(emailRegex)) {
            errori.add("Errore email, riprovare");
        } else if (UtenteDAO.isEmailPresent(email)) {
            errori.add("Email già in utilizzo");
        } else if (telefono == null || telefono.equals("") || !telefono.matches(telRegex)) {
            errori.add("Errore telefono, riprovare");
        }

        if (errori.isEmpty()) {
            Utente u = new Utente();
            u.setNome(nome);
            u.setCognome(cognome);
            u.setPassword(password);
            u.setEmail(email);
            u.setTelefono(telefono);
            u.setImmagine(fileName);
            utenteDAO.addUtente(u);
        }

        return errori;
    }

    public Utente getUserByEmailPassword(String email, String password) throws SQLException {
        return utenteDAO.getUserByEmailPassword(email, password);
    }
}
