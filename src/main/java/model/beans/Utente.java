package model.beans;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;

public class Utente {
    /* @ spec_public @ */
    private int id;
    /* @ spec_public @ */
    private String nome, cognome, email, telefono, password, immagine;
    /* @ spec_public @ */
    private boolean admin;
    /* @ spec_public @ */
    private ArrayList<Ordine> ordini;
    /* @ spec_public @ */
    private ArrayList<Recensione> recensioni;

    /* @ ensures \result == immagine; @ */
    public String getImmagine() {
        return immagine;
    }

    /* @ ensures this.immagine == immagine; @ */
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    public Utente() {
        super();
    }

    /* @ ensures \result == id; @ */
    public int getId() {
        return id;
    }

    /* @ ensures this.id == id; @ */
    public void setId(int id) {
        this.id = id;
    }

    /* @ ensures \result == nome; @ */
    public String getNome() {
        return nome;
    }

    /* @ ensures this.nome == nome; @ */
    public void setNome(String nome) {
        this.nome = nome;
    }

    /* @ ensures \result == cognome; @ */
    public String getCognome() {
        return cognome;
    }

    /* @ ensures this.cognome == cognome; @ */
    public void setCognome(String cognome) {
        this.cognome = cognome;
    }

    /* @ ensures \result == email; @ */
    public String getEmail() {
        return email;
    }

    /* @ ensures this.email == email; @ */
    public void setEmail(String email) {
        this.email = email;
    }

    /* @ ensures \result == telefono; @ */
    public String getTelefono() {
        return telefono;
    }

    /* @ ensures this.telefono == telefono; @ */
    public void setTelefono(String telefono) {
        this.telefono = telefono;
    }

    /* @ ensures \result == admin; @ */
    public boolean isAdmin() {
        return admin;
    }

    /* @ ensures this.admin == admin; @ */
    public void setAdmin(boolean admin) {
        this.admin = admin;
    }

    /* @ ensures \result == ordini; @ */
    public ArrayList<Ordine> getOrdini() {
        return ordini;
    }

    /* @ ensures this.ordini == ordini; @ */
    public void setOrdini(ArrayList<Ordine> ordini) {
        this.ordini = ordini;
    }

    /* @ ensures \result == recensioni; @ */
    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /* @ ensures this.recensioni == recensioni; @ */
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        this.recensioni = recensioni;
    }

    /*
     * @
     * 
     * @ requires password != null;
     * 
     * @ ensures this.password != null;
     * 
     * @
     */
    public void setPassword(String password) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-1");
            digest.reset();
            digest.update(password.getBytes(StandardCharsets.UTF_8));
            this.password = String.format("%040x", new BigInteger(1, digest.digest()));
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    /* @ ensures \result == password; @ */
    public String getPassword() {
        return password;
    }

    /*
     * @
     * 
     * @ requires o != null;
     * 
     * @ ensures \result >= 0;
     * 
     * @
     */
    public int getOrdineIndex(Ordine o) {
        for (Ordine e : ordini) {
            if (e.getId() == o.getId()) {
                return ordini.indexOf(e);
            }
        }
        return 0;
    }
}
