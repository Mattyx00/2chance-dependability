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


    public Ordine() {
        super();
        this.dataOrdine = new Date();
    }

    /*@ ensures \result == this.id; @*/
    public int getId() {
        return id;
    }

    /*@ ensures this.id == id; @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ ensures \result == this.dataOrdine; @*/
    public /*@ pure nullable @*/ Date getDataOrdine() {
        return dataOrdine;
    }

    /*@ 
      @ requires dataOrdine != null;
      @ ensures this.dataOrdine == dataOrdine;
      @*/
    public void setDataOrdine(Date dataOrdine) {
        if (dataOrdine == null) {
            throw new IllegalArgumentException("La data dell'ordine non può essere null");
        }
        this.dataOrdine = dataOrdine;
    }

    /*@ ensures \result == this.indirizzo; @*/
    public /*@ pure nullable @*/ String getIndirizzo() {
        return indirizzo;
    }

    /*@ 
      @ requires indirizzo != null;
      @ ensures this.indirizzo == indirizzo;
      @*/
    public void setIndirizzo(String indirizzo) {
        if (indirizzo == null) {
            throw new IllegalArgumentException("L'indirizzo non può essere null o vuoto");
        }
        boolean empty = true;
        for (int i = 0; i < indirizzo.length(); i++) {
            if (indirizzo.charAt(i) > ' ') {
                empty = false;
                break;
            }
        }
        if (empty) {
            throw new IllegalArgumentException("L'indirizzo non può essere null o vuoto");
        }
        this.indirizzo = indirizzo;
    }

    /*@ ensures \result == this.prezzoTotale; @*/
    public double getPrezzoTotale() {
        return prezzoTotale;
    }

    /*@ 
      @ requires prezzoTotale >= 0;
      @ ensures this.prezzoTotale == prezzoTotale;
      @*/
    public void setPrezzoTotale(double prezzoTotale) {
        if (prezzoTotale < 0) {
            throw new IllegalArgumentException("Il prezzo totale non può essere negativo");
        }
        this.prezzoTotale = prezzoTotale;
    }

    /*@ ensures \result == this.utente; @*/
    public /*@ pure nullable @*/ Utente getUtente() {
        return utente;
    }

    /*@ 
      @ requires utente != null;
      @ ensures this.utente == utente;
      @*/
    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    /*@ ensures \result == this.carrello; @*/
    public /*@ pure nullable @*/ Carrello getCarrello() {
        return carrello;
    }

    /*@ 
      @ requires carrello != null;
      @ ensures this.carrello == carrello;
      @*/
    public void setCarrello(Carrello carrello) {
        if (carrello == null) {
            throw new IllegalArgumentException("Il carrello non può essere null");
        }
        this.carrello = carrello;
    }
}