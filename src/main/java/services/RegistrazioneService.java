package services;

import model.beans.Utente;
import model.dao.UtenteDAO;

import java.sql.SQLException;
import java.util.ArrayList;
import java.util.regex.Pattern;

public class RegistrazioneService {
    private final UtenteDAO utenteDAO;

    // Pre-compiled regex patterns for performance and consistency
    private static final Pattern EMAIL_PATTERN = Pattern.compile("^[\\w-\\.]+@([\\w-]+\\.)+[\\w-]{2,4}$");
    private static final Pattern ONLY_TEXT_PATTERN = Pattern.compile("^[a-zA-Z]*$");
    private static final Pattern TEL_PATTERN = Pattern.compile("^\\d{10}$");
    private static final Pattern PASSWORD_PATTERN = Pattern.compile("^(?=.*[A-Z]).{8,}$");

    public RegistrazioneService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public RegistrazioneService(UtenteDAO utenteDAO) {
        if (utenteDAO == null) {
            throw new IllegalArgumentException("UtenteDAO cannot be null");
        }
        this.utenteDAO = utenteDAO;
    }

    public ArrayList<String> validateAndRegister(String nome, String cognome, String password, String email,
            String telefono, String fileName) throws SQLException {
        // Enforce strict preconditions
        if (nome == null)
            throw new IllegalArgumentException("Nome cannot be null");
        if (cognome == null)
            throw new IllegalArgumentException("Cognome cannot be null");
        if (password == null)
            throw new IllegalArgumentException("Password cannot be null");
        if (email == null)
            throw new IllegalArgumentException("Email cannot be null");
        if (telefono == null)
            throw new IllegalArgumentException("Telefono cannot be null");
        // fileName is treated as an optional input in some contexts, but strict
        // robustness suggests checking it if used.
        // Assuming fileName can be empty but not null for safety.
        if (fileName == null)
            throw new IllegalArgumentException("FileName cannot be null");

        ArrayList<String> errori = new ArrayList<>();

        if (nome.isEmpty() || !ONLY_TEXT_PATTERN.matcher(nome).matches()) {
            errori.add("Errore nome, riprovare");
        }
        if (cognome.isEmpty() || !ONLY_TEXT_PATTERN.matcher(cognome).matches()) {
            errori.add("Errore cognome, riprovare");
        }
        if (password.isEmpty() || !PASSWORD_PATTERN.matcher(password).matches()) {
            errori.add("Errore password, riprovare");
        }
        if (email.isEmpty() || !EMAIL_PATTERN.matcher(email).matches()) {
            errori.add("Errore email, riprovare");
        } else if (UtenteDAO.isEmailPresent(email)) {
            errori.add("Email già in utilizzo");
        }
        if (telefono.isEmpty() || !TEL_PATTERN.matcher(telefono).matches()) {
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
            // Ensure internal state is valid before proceeding (DAO likely throws if
            // invalid, but we checked basics)
            utenteDAO.addUtente(u);
        }

        return errori;
    }

    public Utente getUserByEmailPassword(String email, String password) throws SQLException {
        if (email == null)
            throw new IllegalArgumentException("Email cannot be null");
        if (password == null)
            throw new IllegalArgumentException("Password cannot be null");

        return utenteDAO.getUserByEmailPassword(email, password);
    }
}
