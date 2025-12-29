package model.beans;

import java.util.Date;

public class Ordine {

    /*@ spec_public @*/
    private int id;
    
    /*@ spec_public nullable @*/
    private Date dataOrdine;
    
    /*@ spec_public nullable @*/
    private String indirizzo;
    
    /*@ spec_public @*/
    private double prezzoTotale;
    
    /*@ spec_public nullable @*/
    private Utente utente;
    
    /*@ spec_public nullable @*/
    private Carrello carrello; 

    /*@ public invariant prezzoTotale >= 0; @*/
    /*@ public invariant indirizzo == null || !indirizzo.trim().isEmpty(); @*/

    /*@
      @ assignable \nothing;
      @ ensures id == 0;
      @ ensures prezzoTotale == 0.0;
      @ ensures dataOrdine == null;
      @ ensures indirizzo == null;
      @ ensures utente == null;
      @ ensures carrello == null;
      @*/
    public Ordine() {
        super();
    }

    /*@ 
      @ ensures \result == id; 
      @ pure
      @*/
    public int getId() {
        return id;
    }

    /*@ 
      @ assignable this.id;
      @ ensures this.id == id; 
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ 
      @ ensures \result == dataOrdine;
      @ pure 
      @*/
    public Date getDataOrdine() {
        return dataOrdine;
    }

    /*@
      @ public normal_behavior
      @   requires dataOrdine != null;
      @   assignable this.dataOrdine;
      @   ensures this.dataOrdine == dataOrdine;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires dataOrdine == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setDataOrdine(Date dataOrdine) {
        if (dataOrdine == null) {
            throw new IllegalArgumentException("La data dell'ordine non può essere null");
        }
        this.dataOrdine = dataOrdine;
    }

    /*@ 
      @ ensures \result == indirizzo;
      @ pure 
      @*/
    public String getIndirizzo() {
        return indirizzo;
    }

    /*@
      @ public normal_behavior
      @   requires indirizzo != null && !indirizzo.trim().isEmpty();
      @   assignable this.indirizzo;
      @   ensures this.indirizzo == indirizzo;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires indirizzo == null || indirizzo.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setIndirizzo(String indirizzo) {
        if (indirizzo == null || indirizzo.trim().isEmpty()) {
            throw new IllegalArgumentException("L'indirizzo non può essere null o vuoto");
        }
        this.indirizzo = indirizzo;
    }

    /*@ 
      @ ensures \result == prezzoTotale;
      @ pure 
      @*/
    public double getPrezzoTotale() {
        return prezzoTotale;
    }

    /*@
      @ public normal_behavior
      @   requires prezzoTotale >= 0;
      @   assignable this.prezzoTotale;
      @   ensures this.prezzoTotale == prezzoTotale;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires prezzoTotale < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setPrezzoTotale(double prezzoTotale) {
        if (prezzoTotale < 0) {
            throw new IllegalArgumentException("Il prezzo totale non può essere negativo");
        }
        this.prezzoTotale = prezzoTotale;
    }

    /*@ 
      @ ensures \result == utente;
      @ pure 
      @*/
    public Utente getUtente() {
        return utente;
    }

    /*@
      @ public normal_behavior
      @   requires utente != null;
      @   assignable this.utente;
      @   ensures this.utente == utente;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires utente == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    /*@ 
      @ ensures \result == carrello;
      @ pure 
      @*/
    public Carrello getCarrello() {
        return carrello;
    }

    /*@
      @ public normal_behavior
      @   requires carrello != null;
      @   assignable this.carrello;
      @   ensures this.carrello == carrello;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires carrello == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setCarrello(Carrello carrello) {
        if (carrello == null) {
            throw new IllegalArgumentException("Il carrello non può essere null");
        }
        this.carrello = carrello;
    }
}