package model.beans;

public class ProdottoCarrello {
    /*@ spec_public nullable @*/
    private Prodotto prodotto;
    /*@ spec_public @*/
    private int quantita;

    /*@ public invariant quantita >= 0; @*/

    /*@
      @ public normal_behavior
      @   assignable this.prodotto, this.quantita;
      @   ensures this.prodotto == null;
      @   ensures this.quantita == 0;
      @*/
    public ProdottoCarrello() {

    }

    /*@
      @ public normal_behavior
      @   requires prodotto != null;
      @   requires quantita >= 0;
      @   assignable this.prodotto, this.quantita;
      @   ensures this.prodotto == prodotto;
      @   ensures this.quantita == quantita;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires prodotto == null;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires quantita < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
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
      @ ensures \result == this.prodotto;
      @ pure
      @*/
    public Prodotto getProdotto() {
        return prodotto;
    }

    /*@
      @ ensures \result == this.quantita;
      @ pure
      @*/
    public int getQuantita() {
        return quantita;
    }

    /*@
      @ public normal_behavior
      @   requires this.prodotto != null;
      @   ensures \result == this.prodotto.getPrezzo() * this.quantita;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires this.prodotto == null;
      @   assignable \nothing;
      @   signals (IllegalStateException e) true;
      @
      @ pure
      @*/
    public double getPrezzoTotale() {
        if (prodotto == null) {
            throw new IllegalStateException("Impossibile calcolare il prezzo totale: prodotto non impostato");
        }
        return prodotto.getPrezzo() * quantita;
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

    /*@
      @ public normal_behavior
      @   requires quantita >= 0;
      @   assignable this.quantita;
      @   ensures this.quantita == quantita;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires quantita < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setQuantita(int quantita) {
        if (quantita < 0) {
            throw new IllegalArgumentException("La quantità non può essere negativa");
        }
        this.quantita = quantita;
    }
}
