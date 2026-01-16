package model.beans;

public class ProdottoCarrello {
    /*@ spec_public non_null @*/ private Prodotto prodotto;
    /*@ spec_public @*/ private int quantita;

    //@ public invariant quantita >= 0;

    /*@
      @ ensures quantita == 0;
      @*/
    public ProdottoCarrello() {
        this.prodotto = new Prodotto();
        this.quantita = 0;
    }

    /*@
      @ requires prodotto != null;
      @ requires quantita >= 0;
      @ ensures this.prodotto == prodotto;
      @ ensures this.quantita == quantita;
      @*/
    public ProdottoCarrello(Prodotto prodotto, int quantita) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        if (quantita < 0) {
            throw new IllegalArgumentException("La quantità non può essere negativa");
        }
        this.prodotto = prodotto;
        this.quantita = quantita;
    }

    /*@
      @ ensures \result == prodotto;
      @*/
    public /*@ pure @*/ Prodotto getProdotto() {
        return prodotto;
    }

    /*@
      @ ensures \result == quantita;
      @*/
    public /*@ pure @*/ int getQuantita() {
        return quantita;
    }

    /*@
      @ requires prodotto != null;
      @ ensures \result == prodotto.getPrezzo() * quantita;
      @*/
    public /*@ pure @*/ double getPrezzoTotale() {
        if (prodotto == null) {
            throw new IllegalStateException("Impossibile calcolare il prezzo totale: prodotto non impostato");
        }
        return prodotto.getPrezzo() * quantita;
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

    /*@
      @ requires quantita >= 0;
      @ ensures this.quantita == quantita;
      @ assignable this.quantita;
      @*/
    public void setQuantita(int quantita) {
        if (quantita < 0) {
            throw new IllegalArgumentException("La quantità non può essere negativa");
        }
        this.quantita = quantita;
    }
}
