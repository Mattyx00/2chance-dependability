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
    private String nome, cognome, email, telefono, password, immagine;
    
    /*@ spec_public @*/
    private boolean admin;
    
    /*@ spec_public nullable @*/
    private ArrayList<Ordine> ordini;
    
    /*@ spec_public nullable @*/
    private ArrayList<Recensione> recensioni;

    /*@ 
      @ ensures \result == this.immagine;
      @ pure
      @*/
    public String getImmagine() {
        return immagine;
    }

    /*@ 
      @ requires true;
      @ assignable this.immagine;
      @ ensures this.immagine == immagine;
      @*/
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    /*@
      @ public normal_behavior
      @   assignable \nothing;
      @   ensures this.id == 0;
      @   ensures this.nome == null;
      @   ensures this.cognome == null;
      @   ensures this.email == null;
      @   ensures this.telefono == null;
      @   ensures this.password == null;
      @   ensures this.immagine == null;
      @   ensures this.admin == false;
      @   ensures this.ordini == null;
      @   ensures this.recensioni == null;
      @*/
    public Utente() {
        super();
    }

    /*@ 
      @ ensures \result == this.id;
      @ pure
      @*/
    public int getId() {
        return id;
    }

    /*@ 
      @ requires true;
      @ assignable this.id;
      @ ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ 
      @ ensures \result == this.nome;
      @ pure
      @*/
    public String getNome() {
        return nome;
    }

    /*@ 
      @ public normal_behavior
      @   requires nome != null && !nome.trim().isEmpty();
      @   assignable this.nome;
      @   ensures this.nome == nome;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires nome == null || nome.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setNome(String nome) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /*@ 
      @ ensures \result == this.cognome;
      @ pure
      @*/
    public String getCognome() {
        return cognome;
    }

    /*@ 
      @ public normal_behavior
      @   requires cognome != null && !cognome.trim().isEmpty();
      @   assignable this.cognome;
      @   ensures this.cognome == cognome;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires cognome == null || cognome.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setCognome(String cognome) {
        if (cognome == null || cognome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il cognome non può essere null o vuoto");
        }
        this.cognome = cognome;
    }

    /*@ 
      @ ensures \result == this.email;
      @ pure
      @*/
    public String getEmail() {
        return email;
    }

    /*@ 
      @ public normal_behavior
      @   requires email != null && !email.trim().isEmpty();
      @   assignable this.email;
      @   ensures this.email == email;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires email == null || email.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setEmail(String email) {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("L'email non può essere null o vuota");
        }
        this.email = email;
    }

    /*@ 
      @ ensures \result == this.telefono;
      @ pure
      @*/
    public String getTelefono() {
        return telefono;
    }

    /*@ 
      @ public normal_behavior
      @   requires telefono != null && !telefono.trim().isEmpty();
      @   assignable this.telefono;
      @   ensures this.telefono == telefono;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires telefono == null || telefono.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setTelefono(String telefono) {
        if (telefono == null || telefono.trim().isEmpty()) {
            throw new IllegalArgumentException("Il telefono non può essere null o vuoto");
        }
        this.telefono = telefono;
    }

    /*@ 
      @ ensures \result == this.admin;
      @ pure
      @*/
    public boolean isAdmin() {
        return admin;
    }

    /*@ 
      @ requires true;
      @ assignable this.admin;
      @ ensures this.admin == admin;
      @*/
    public void setAdmin(boolean admin) {
        this.admin = admin;
    }

    /*@ 
      @ ensures \result == this.ordini;
      @ pure
      @*/
    public ArrayList<Ordine> getOrdini() {
        return ordini;
    }

    /*@ 
      @ public normal_behavior
      @   requires ordini != null;
      @   assignable this.ordini;
      @   ensures this.ordini == ordini;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires ordini == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setOrdini(ArrayList<Ordine> ordini) {
        if (ordini == null) {
            throw new IllegalArgumentException("La lista degli ordini non può essere null");
        }
        this.ordini = ordini;
    }

    /*@ 
      @ ensures \result == this.recensioni;
      @ pure
      @*/
    public ArrayList<Recensione> getRecensioni() {
        return recensioni;
    }

    /*@ 
      @ public normal_behavior
      @   requires recensioni != null;
      @   assignable this.recensioni;
      @   ensures this.recensioni == recensioni;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires recensioni == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setRecensioni(ArrayList<Recensione> recensioni) {
        if (recensioni == null) {
            throw new IllegalArgumentException("La lista delle recensioni non può essere null");
        }
        this.recensioni = recensioni;
    }

    /*@ 
      @ public normal_behavior
      @   requires password != null && !password.trim().isEmpty();
      @   assignable this.password;
      @   ensures this.password != null;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires password == null || password.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
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

    /*@ 
      @ ensures \result == this.password;
      @ pure
      @*/
    public String getPassword() {
        return password;
    }

    /*@ 
      @ public normal_behavior
      @   requires o != null;
      @   requires ordini == null;
      @   assignable \nothing;
      @   ensures \result == -1;
      @
      @ also
      @
      @ public normal_behavior
      @   requires o != null;
      @   requires ordini != null;
      @   assignable \nothing;
      @   ensures \result >= -1; 
      @   ensures \result < ordini.size();
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires o == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @
      @ pure
      @*/
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
