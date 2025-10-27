package model.beans;

public class ProdottoCarrello {
    private  Prodotto prodotto;
    private  int quantita;

    public ProdottoCarrello() {

    }

    public Prodotto getProdotto() {
        return prodotto;
    }

    public int getQuantita() {
        return quantita;
    }

    public double getPrezzoTotale(){
        return prodotto.getPrezzo() * quantita;
    }

    public void setProdotto(Prodotto prodotto) {
        this.prodotto = prodotto;
    }

    public void setQuantita(int quantita) {
        this.quantita = quantita;
    }
}
