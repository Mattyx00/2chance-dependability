package model.beans;

public class ProdottoCarrello {
    private Prodotto prodotto;
    private int quantita;


    public ProdottoCarrello() {

    }

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

    public Prodotto getProdotto() {
        return prodotto;
    }

    public int getQuantita() {
        return quantita;
    }

    public double getPrezzoTotale() {
        if (prodotto == null) {
            throw new IllegalStateException("Impossibile calcolare il prezzo totale: prodotto non impostato");
        }
        return prodotto.getPrezzo() * quantita;
    }

    public void setProdotto(Prodotto prodotto) {
        if (prodotto == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        this.prodotto = prodotto;
    }

    public void setQuantita(int quantita) {
        if (quantita < 0) {
            throw new IllegalArgumentException("La quantità non può essere negativa");
        }
        this.quantita = quantita;
    }
}
