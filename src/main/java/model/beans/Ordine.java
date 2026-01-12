package model.beans;

import java.util.Date;

public class Ordine {

    private int id;
    
    private Date dataOrdine;
    
    private String indirizzo;
    
    private double prezzoTotale;
    
    private Utente utente;
    
    private Carrello carrello; 


    public Ordine() {
        super();
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public Date getDataOrdine() {
        return dataOrdine;
    }

    public void setDataOrdine(Date dataOrdine) {
        if (dataOrdine == null) {
            throw new IllegalArgumentException("La data dell'ordine non può essere null");
        }
        this.dataOrdine = dataOrdine;
    }

    public String getIndirizzo() {
        return indirizzo;
    }

    public void setIndirizzo(String indirizzo) {
        if (indirizzo == null || indirizzo.trim().isEmpty()) {
            throw new IllegalArgumentException("L'indirizzo non può essere null o vuoto");
        }
        this.indirizzo = indirizzo;
    }

    public double getPrezzoTotale() {
        return prezzoTotale;
    }

    public void setPrezzoTotale(double prezzoTotale) {
        if (prezzoTotale < 0) {
            throw new IllegalArgumentException("Il prezzo totale non può essere negativo");
        }
        this.prezzoTotale = prezzoTotale;
    }

    public Utente getUtente() {
        return utente;
    }

    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    public Carrello getCarrello() {
        return carrello;
    }

    public void setCarrello(Carrello carrello) {
        if (carrello == null) {
            throw new IllegalArgumentException("Il carrello non può essere null");
        }
        this.carrello = carrello;
    }
}