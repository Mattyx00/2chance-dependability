package model.beans;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;

public class Utente {
    /*@ spec_public @*/
    private int id;
    
    /*@ spec_public nullable @*/
    private String nome, cognome, email, telefono, password;
    
    /*@ spec_public nullable @*/
    private String immagine;
    
    /*@ spec_public @*/
    private boolean admin;
    
    /*@ spec_public nullable @*/
    private ArrayList<Ordine> ordini;
    
    /*@ spec_public nullable @*/
    private ArrayList<Recensione> recensioni;



    /*@ ensures \result == this.immagine; @*/
    public /*@ pure nullable @*/ String getImmagine() {
        return immagine;
    }

    /*@ ensures this.immagine == immagine; @*/
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    public Utente() {
        super();
        this.nome = "";
        this.cognome = "";
        this.email = "";
        this.telefono = "";
        this.password = "";
        this.immagine = "";
        this.ordini = new ArrayList<>();
        this.recensioni = new ArrayList<>();
    }

    /*@ ensures \result == this.id; @*/
    public int getId() {
        return id;
    }

    /*@ ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ ensures \result == this.nome; @*/
    public /*@ pure nullable @*/ String getNome() {
        return nome;
    }

    /*@ 
      @ ensures this.nome == nome; 

      @*/
    public void setNome(String nome) {
        boolean empty = true;
        if (nome != null) {
            for (int i = 0; i < nome.length(); i++) {
                if (nome.charAt(i) > ' ') {
                    empty = false;
                    break;
                }
            }
        }
        if (empty) {
            throw new IllegalArgumentException("Il nome non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /*@ ensures \result == this.cognome; @*/
    public /*@ pure nullable @*/ String getCognome() {
        return cognome;
    }

    /*@ 
      @ ensures this.cognome == cognome; 

      @*/
    public void setCognome(String cognome) {
        boolean empty = true;
        if (cognome != null) {
            for (int i = 0; i < cognome.length(); i++) {
                if (cognome.charAt(i) > ' ') {
                    empty = false;
                    break;
                }
            }
        }
        if (empty) {
            throw new IllegalArgumentException("Il cognome non può essere null o vuoto");
        }
        this.cognome = cognome;
    }

    /*@ ensures \result == this.email; @*/
    public /*@ pure nullable @*/ String getEmail() {
        return email;
    }

    /*@ 
      @ ensures this.email == email; 

      @*/
    public void setEmail(String email) {
        boolean empty = true;
        if (email != null) {
            for (int i = 0; i < email.length(); i++) {
                if (email.charAt(i) > ' ') {
                    empty = false;
                    break;
                }
            }
        }
        if (empty) {
            throw new IllegalArgumentException("L'email non può essere null o vuota");
        }
        this.email = email;
    }

    /*@ ensures \result == this.telefono; @*/
    public /*@ pure nullable @*/ String getTelefono() {
        return telefono;
    }

    /*@ 
      @ ensures this.telefono == telefono; 

      @*/
    public void setTelefono(String telefono) {
        boolean empty = true;
        if (telefono != null) {
            for (int i = 0; i < telefono.length(); i++) {
                if (telefono.charAt(i) > ' ') {
                    empty = false;
                    break;
                }
            }
        }
        if (empty) {
            throw new IllegalArgumentException("Il telefono non può essere null o vuoto");
        }
        this.telefono = telefono;
    }

    /*@ ensures \result == this.admin; @*/
    public boolean isAdmin() {
        return admin;
    }

    /*@ ensures this.admin == admin; @*/
    public void setAdmin(boolean admin) {
        this.admin = admin;
    }

    /*@ ensures \result == this.ordini; @*/
    public /*@ pure nullable @*/ ArrayList<Ordine> getOrdini() {
        return ordini;
    }

    /*@ 
      @ ensures this.ordini == ordini; 

      @*/
    public void setOrdini(ArrayList<Ordine> ordini) {
        if (ordini == null) {
            throw new IllegalArgumentException("La lista degli ordini non può essere null");
        }
        this.ordini = ordini;
    }

    /*@ ensures \result == this.recensioni; @*/
    public /*@ pure nullable @*/ ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*@ 
      @ ensures this.recensioni == recensioni; 

      @*/
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    public void setPassword(String password) {
        boolean empty = true;
        if (password != null) {
            for (int i = 0; i < password.length(); i++) {
                if (password.charAt(i) > ' ') {
                    empty = false;
                    break;
                }
            }
        }
        if (empty) {
            throw new IllegalArgumentException("La password non può essere null o vuota");
        }
        this.password = hashPassword(password);
    }

    /*@
      @ private behavior
      @ requires password != null;
      @ ensures \result != null;
      @ assignable \nothing;
      @*/
    private /*@ helper @*/ String hashPassword(String password) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-1");
            digest.reset();
            digest.update(password.getBytes(StandardCharsets.UTF_8));
            byte[] hash = digest.digest();

            //@ assume hash != null && hash.length > 0;
            //@ assume (\exists int k; 0 <= k && k < hash.length; hash[k] != 0);

            return String.format("%040x", new BigInteger(1, hash));
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ ensures \result == this.password; @*/
    public /*@ pure nullable @*/ String getPassword() {
        return password;
    }

    /*@ 
      @ requires o != null;
      @ ensures \result >= -1;
      @*/
    public int getOrdineIndex(Ordine o) {
        /*@ assume ordini != null; @*/
        if (o == null) {
            throw new IllegalArgumentException("L'ordine non può essere null");
        }
        if (ordini == null) {
            return -1;
        }
        for (int i = 0; i < ordini.size(); i++) {
            Ordine e = ordini.get(i);
            if (e.getId() == o.getId()) {
                return i;
            }
        }
        return -1;
    }
}
