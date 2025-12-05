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

    /*
     * @
     * 
     * @ requires utente != null;
     * 
     * @ requires prodotto != null;
     * 
     * @ requires valutazione >= 1 && valutazione <= 5;
     * 
     * @ requires testo != null && !testo.trim().isEmpty();
     * 
     * @ requires dataRecensione != null;
     * 
     * @ ensures this.utente == utente && this.prodotto == prodotto;
     * 
     * @ ensures this.valutazione == valutazione && this.testo == testo;
     * 
     * @ ensures this.dataRecensione == dataRecensione;
     * 
     * @
     */
    public Recensione(Utente utente, Prodotto prodotto, int valutazione, String testo, Date dataRecensione) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5");
        }
        if (testo == null || testo.trim().isEmpty()) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        if (dataRecensione == null) {
            throw new IllegalArgumentException("La data della recensione non può essere null");
        }
        this.utente = utente;
        this.prodotto = prodotto;
        this.valutazione = valutazione;
        this.testo = testo;
        this.dataRecensione = dataRecensione;
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
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5");
        }
        this.valutazione = valutazione;
    }

    /* @ ensures \result == dataRecensione; @ */
    public Date getDataRecensione() {
        return dataRecensione;
    }

    /*
     * @
     * 
     * @ requires dataRecensione != null;
     * 
     * @ ensures this.dataRecensione == dataRecensione;
     * 
     * @
     */
    public void setDataRecensione(Date dataRecensione) {
        if (dataRecensione == null) {
            throw new IllegalArgumentException("La data della recensione non può essere null");
        }
        this.dataRecensione = dataRecensione;
    }

    /* @ ensures \result == testo; @ */
    public String getTesto() {
        return testo;
    }

    /*
     * @
     * 
     * @ requires testo != null && !testo.trim().isEmpty();
     * 
     * @ ensures this.testo == testo;
     * 
     * @
     */
    public void setTesto(String testo) {
        if (testo == null || testo.trim().isEmpty()) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        this.testo = testo;
    }

    /* @ ensures \result == utente; @ */
    public Utente getUtente() {
        return utente;
    }

    /*
     * @
     * 
     * @ requires utente != null;
     * 
     * @ ensures this.utente == utente;
     * 
     * @
     */
    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    /* @ ensures \result == prodotto; @ */
    public Prodotto getProdotto() {
        return prodotto;
    }

    /*
     * @
     * 
     * @ requires prodotto != null;
     * 
     * @ ensures this.prodotto == prodotto;
     * 
     * @
     */
    public void setProdotto(Prodotto prodotto) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        this.prodotto = prodotto;
    }
}
