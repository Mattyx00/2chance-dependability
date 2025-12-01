package model.beans;

import java.util.Date;

public class Recensione {
    /* @ spec_public @ */
    private int id, valutazione;
    /* @ spec_public @ */
    private Date dataRecensione;
    /* @ spec_public @ */
    private String testo;
    /* @ spec_public @ */
    private Utente utente;
    /* @ spec_public @ */
    private Prodotto prodotto;

    /* @ public invariant valutazione >= 1 && valutazione <= 5; @ */

    public Recensione() {
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

    /* @ ensures \result == valutazione; @ */
    public int getValutazione() {
        return valutazione;
    }

    /*
     * @
     * 
     * @ requires valutazione >= 1 && valutazione <= 5;
     * 
     * @ ensures this.valutazione == valutazione;
     * 
     * @
     */
    public void setValutazione(int valutazione) {
        this.valutazione = valutazione;
    }

    /* @ ensures \result == dataRecensione; @ */
    public Date getDataRecensione() {
        return dataRecensione;
    }

    /* @ ensures this.dataRecensione == dataRecensione; @ */
    public void setDataRecensione(Date dataRecensione) {
        this.dataRecensione = dataRecensione;
    }

    /* @ ensures \result == testo; @ */
    public String getTesto() {
        return testo;
    }

    /* @ ensures this.testo == testo; @ */
    public void setTesto(String testo) {
        this.testo = testo;
    }

    /* @ ensures \result == utente; @ */
    public Utente getUtente() {
        return utente;
    }

    /* @ ensures this.utente == utente; @ */
    public void setUtente(Utente utente) {
        this.utente = utente;
    }

    /* @ ensures \result == prodotto; @ */
    public Prodotto getProdotto() {
        return prodotto;
    }

    /* @ ensures this.prodotto == prodotto; @ */
    public void setProdotto(Prodotto prodotto) {
        this.prodotto = prodotto;
    }
}
