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

    /*
     * @
     * 
     * @ requires nome != null && !nome.trim().isEmpty();
     * 
     * @ ensures this.nome == nome;
     * 
     * @
     */
    public void setNome(String nome) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /* @ ensures \result == cognome; @ */
    public String getCognome() {
        return cognome;
    }

    /*
     * @
     * 
     * @ requires cognome != null && !cognome.trim().isEmpty();
     * 
     * @ ensures this.cognome == cognome;
     * 
     * @
     */
    public void setCognome(String cognome) {
        if (cognome == null || cognome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il cognome non può essere null o vuoto");
        }
        this.cognome = cognome;
    }

    /* @ ensures \result == email; @ */
    public String getEmail() {
        return email;
    }

    /*
     * @
     * 
     * @ requires email != null && !email.trim().isEmpty();
     * 
     * @ ensures this.email == email;
     * 
     * @
     */
    public void setEmail(String email) {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("L'email non può essere null o vuota");
        }
        this.email = email;
    }

    /* @ ensures \result == telefono; @ */
    public String getTelefono() {
        return telefono;
    }

    /*
     * @
     * 
     * @ requires telefono != null && !telefono.trim().isEmpty();
     * 
     * @ ensures this.telefono == telefono;
     * 
     * @
     */
    public void setTelefono(String telefono) {
        if (telefono == null || telefono.trim().isEmpty()) {
            throw new IllegalArgumentException("Il telefono non può essere null o vuoto");
        }
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

    /*
     * @
     * 
     * @ requires ordini != null;
     * 
     * @ ensures this.ordini == ordini;
     * 
     * @
     */
    public void setOrdini(ArrayList<Ordine> ordini) {
        if (ordini == null) {
            throw new IllegalArgumentException("La lista degli ordini non può essere null");
        }
        this.ordini = ordini;
    }

    /* @ ensures \result == recensioni; @ */
    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*
     * @
     * 
     * @ requires recensioni != null;
     * 
     * @ ensures this.recensioni == recensioni;
     * 
     * @
     */
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
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
        if (password == null || password.trim().isEmpty()) {
            throw new IllegalArgumentException("La password non può essere null o vuota");
        }
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
     * @ ensures \result >= -1;
     * 
     * @
     */
    public int getOrdineIndex(Ordine o) {
        if (o == null) {
            throw new IllegalArgumentException("L'ordine non può essere null");
        }
        if (ordini == null) {
            return -1;
        }
        for (Ordine e : ordini) {
            if (e.getId() == o.getId()) {
                return ordini.indexOf(e);
            }
        }
        return -1;
    }
}
