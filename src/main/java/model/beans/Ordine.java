package model.beans;

import java.util.Date;

public class Ordine {
    /* @ spec_public @ */
    private int id;
    /* @ spec_public @ */
    private Date dataOrdine;
    /* @ spec_public @ */
    private String indirizzo;
    /* @ spec_public @ */
    private double prezzoTotale;
    /* @ spec_public @ */
    private Utente utente;
    /* @ spec_public @ */
    private Carrello carrello; // riferimento al carrello, per intervenire sulla tabella associativa(Composto)

    /* @ public invariant prezzoTotale >= 0; @ */

    public Ordine() {
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

    /* @ ensures \result == dataOrdine; @ */
    public Date getDataOrdine() {
        return dataOrdine;
    }

    /* @ ensures this.dataOrdine == dataOrdine; @ */
    public void setDataOrdine(Date dataOrdine) {
        this.dataOrdine = dataOrdine;
    }

    /* @ ensures \result == indirizzo; @ */
    public String getIndirizzo() {
        return indirizzo;
    }

    /* @ ensures this.indirizzo == indirizzo; @ */
    public void setIndirizzo(String indirizzo) {
        this.indirizzo = indirizzo;
    }

    /* @ ensures \result == prezzoTotale; @ */
    public double getPrezzoTotale() {
        return prezzoTotale;
    }

    /*
     * @
     * 
     * @ requires prezzoTotale >= 0;
     * 
     * @ ensures this.prezzoTotale == prezzoTotale;
     * 
     * @
     */
    public void setPrezzoTotale(double prezzoTotale) {
        this.prezzoTotale = prezzoTotale;
    }

    /* @ ensures \result == utente; @ */
    public Utente getUtente() {
        return utente;
    }

    /* @ ensures this.utente == utente; @ */
    public void setUtente(Utente utente) {
        this.utente = utente;
    }

    /* @ ensures \result == carrello; @ */
    public Carrello getCarrello() {
        return carrello;
    }

    /* @ ensures this.carrello == carrello; @ */
    public void setCarrello(Carrello carrello) {
        this.carrello = carrello;
    }
}
