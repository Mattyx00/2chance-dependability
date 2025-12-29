package model.beans;

import java.util.Date;

public class Recensione {
    /*@ spec_public @*/
    private int id;
    /*@ spec_public @*/
    private int valutazione;
    /*@ spec_public nullable @*/
    private Date dataRecensione;
    /*@ spec_public nullable @*/
    private String testo;
    /*@ spec_public nullable @*/
    private Utente utente;
    /*@ spec_public nullable @*/
    private Prodotto prodotto;

    /*@ public invariant valutazione >= 0 && valutazione <= 5; @*/

    /*@
      @ public behavior
      @   assignable \nothing;
      @   ensures this.id == 0;
      @   ensures this.valutazione == 0;
      @   ensures this.dataRecensione == null;
      @   ensures this.testo == null;
      @   ensures this.utente == null;
      @   ensures this.prodotto == null;
      @*/
    public Recensione() {
        super();
    }

/*@
      @ public normal_behavior
      @   requires utente != null;
      @   requires prodotto != null;
      @   requires valutazione >= 1 && valutazione <= 5;
      @   requires testo != null && !testo.trim().isEmpty();
      @   requires dataRecensione != null;
      @   assignable this.utente, this.prodotto, this.valutazione, this.testo, this.dataRecensione;
      @   ensures this.utente == utente;
      @   ensures this.prodotto == prodotto;
      @   ensures this.valutazione == valutazione;
      @   ensures this.testo == testo;
      @   ensures this.dataRecensione == dataRecensione;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires utente == null || 
      @            prodotto == null || 
      @            (valutazione < 1 || valutazione > 5) || 
      @            (testo == null || testo.trim().isEmpty()) || 
      @            dataRecensione == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
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

    /*@ 
      @ ensures \result == id;
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
      @ ensures \result == valutazione;
      @ pure 
      @*/
    public int getValutazione() {
        return valutazione;
    }

    /*@
      @ public normal_behavior
      @   requires valutazione >= 1 && valutazione <= 5;
      @   assignable this.valutazione;
      @   ensures this.valutazione == valutazione;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires valutazione < 1 || valutazione > 5;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setValutazione(int valutazione) {
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5");
        }
        this.valutazione = valutazione;
    }

    /*@ 
      @ ensures \result == dataRecensione;
      @ pure
      @*/
    public Date getDataRecensione() {
        return dataRecensione;
    }

    /*@
      @ public normal_behavior
      @   requires dataRecensione != null;
      @   assignable this.dataRecensione;
      @   ensures this.dataRecensione == dataRecensione;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires dataRecensione == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setDataRecensione(Date dataRecensione) {
        if (dataRecensione == null) {
            throw new IllegalArgumentException("La data della recensione non può essere null");
        }
        this.dataRecensione = dataRecensione;
    }

    /*@ 
      @ ensures \result == testo;
      @ pure
      @*/
    public String getTesto() {
        return testo;
    }

    /*@
      @ public normal_behavior
      @   requires testo != null && !testo.trim().isEmpty();
      @   assignable this.testo;
      @   ensures this.testo == testo;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires testo == null || testo.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setTesto(String testo) {
        if (testo == null || testo.trim().isEmpty()) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        this.testo = testo;
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
      @ ensures \result == prodotto;
      @ pure
      @*/
    public Prodotto getProdotto() {
        return prodotto;
    }

    /*@
      @ public normal_behavior
      @   requires prodotto != null;
      @   assignable this.prodotto;
      @   ensures this.prodotto == prodotto;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires prodotto == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setProdotto(Prodotto prodotto) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        this.prodotto = prodotto;
    }
}
