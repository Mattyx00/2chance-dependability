package model.beans;

import java.util.Date;

public class Recensione {
    private /*@ spec_public @*/ int id;
    private /*@ spec_public @*/ int valutazione;
    private /*@ spec_public nullable @*/ Date dataRecensione;
    private /*@ spec_public nullable @*/ String testo;
    private /*@ spec_public nullable @*/ Utente utente;
    private /*@ spec_public nullable @*/ Prodotto prodotto;

    //@ public invariant valutazione >= 1 && valutazione <= 5;

    public Recensione() {
        super();
        this.dataRecensione = new Date();
        this.valutazione = 1;
    }

    /*@
      @ requires utente != null;
      @ requires prodotto != null;
      @ requires valutazione >= 1 && valutazione <= 5;
      @ requires testo != null;
      @ requires dataRecensione != null;
      @ ensures this.utente == utente;
      @ ensures this.prodotto == prodotto;
      @ ensures this.valutazione == valutazione;
      @ ensures this.testo == testo;
      @ ensures this.dataRecensione == dataRecensione;
      @*/
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
        if (testo == null) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        boolean isAllWhitespace = true;
        for (int i = 0; i < testo.length(); i++) {
            if (testo.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
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

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public int getValutazione() {
        return valutazione;
    }

    /*@
      @ requires valutazione >= 1 && valutazione <= 5;
      @ ensures this.valutazione == valutazione;
      @*/
    public void setValutazione(int valutazione) {
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5");
        }
        this.valutazione = valutazione;
    }

    public /*@ pure nullable @*/ Date getDataRecensione() {
        return dataRecensione;
    }

    /*@
      @ requires dataRecensione != null;
      @ ensures this.dataRecensione == dataRecensione;
      @*/
    public void setDataRecensione(Date dataRecensione) {
        if (dataRecensione == null) {
            throw new IllegalArgumentException("La data della recensione non può essere null");
        }
        this.dataRecensione = dataRecensione;
    }

    public /*@ pure nullable @*/ String getTesto() {
        return testo;
    }

    /*@
      @ requires testo != null;
      @ ensures this.testo == testo;
      @*/
    public void setTesto(String testo) {
        if (testo == null) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        boolean isAllWhitespace = true;
        for (int i = 0; i < testo.length(); i++) {
            if (testo.charAt(i) > ' ') {
                isAllWhitespace = false;
                break;
            }
        }
        if (isAllWhitespace) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        this.testo = testo;
    }

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

    public /*@ pure nullable @*/ Prodotto getProdotto() {
        return prodotto;
    }

    /*@
      @ requires prodotto != null;
      @ ensures this.prodotto == prodotto;
      @*/
    public void setProdotto(Prodotto prodotto) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        this.prodotto = prodotto;
    }
}
