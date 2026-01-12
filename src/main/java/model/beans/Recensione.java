package model.beans;

import java.util.Date;

public class Recensione {
    private int id;
    private int valutazione;
    private Date dataRecensione;
    private String testo;
    private Utente utente;
    private Prodotto prodotto;


    public Recensione() {
        super();
    }

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

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public int getValutazione() {
        return valutazione;
    }

    public void setValutazione(int valutazione) {
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5");
        }
        this.valutazione = valutazione;
    }

    public Date getDataRecensione() {
        return dataRecensione;
    }

    public void setDataRecensione(Date dataRecensione) {
        if (dataRecensione == null) {
            throw new IllegalArgumentException("La data della recensione non può essere null");
        }
        this.dataRecensione = dataRecensione;
    }

    public String getTesto() {
        return testo;
    }

    public void setTesto(String testo) {
        if (testo == null || testo.trim().isEmpty()) {
            throw new IllegalArgumentException("Il testo della recensione non può essere null o vuoto");
        }
        this.testo = testo;
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

    public Prodotto getProdotto() {
        return prodotto;
    }

    public void setProdotto(Prodotto prodotto) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        this.prodotto = prodotto;
    }
}
