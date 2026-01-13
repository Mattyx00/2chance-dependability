package model.beans;

public class Specifiche {

    /*@ spec_public nullable @*/
    private String nome, valore;

    public Specifiche() {
        super();
    }

    /*@
      @ requires nome != null;
      @ requires (\exists int i; 0 <= i < nome.length(); nome.charAt(i) > ' ');
      @ requires valore != null;
      @ requires (\exists int i; 0 <= i < valore.length(); valore.charAt(i) > ' ');
      @ ensures this.nome == nome;
      @ ensures this.valore == valore;
      @*/
    public Specifiche(String nome, String valore) {
        boolean nomeHasContent = false;
        if (nome != null) {
            for (int i = 0; i < nome.length(); i++) {
                if (nome.charAt(i) > ' ') {
                    nomeHasContent = true;
                    break;
                }
            }
        }
        if (nome == null || !nomeHasContent) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }

        boolean valoreHasContent = false;
        if (valore != null) {
            for (int i = 0; i < valore.length(); i++) {
                if (valore.charAt(i) > ' ') {
                    valoreHasContent = true;
                    break;
                }
            }
        }
        if (valore == null || !valoreHasContent) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.nome = nome;
        this.valore = valore;
    }

    /*@ pure @*/
    public /*@ nullable @*/ String getNome() {
        return nome;
    }

    /*@
      @ requires nome != null;
      @ requires (\exists int i; 0 <= i < nome.length(); nome.charAt(i) > ' ');
      @ ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        boolean nomeHasContent = false;
        if (nome != null) {
            for (int i = 0; i < nome.length(); i++) {
                if (nome.charAt(i) > ' ') {
                    nomeHasContent = true;
                    break;
                }
            }
        }
        if (nome == null || !nomeHasContent) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /*@ pure @*/
    public /*@ nullable @*/ String getValore() {
        return valore;
    }

    /*@
      @ requires valore != null;
      @ requires (\exists int i; 0 <= i < valore.length(); valore.charAt(i) > ' ');
      @ ensures this.valore == valore;
      @*/
    public void setValore(String valore) {
        boolean valoreHasContent = false;
        if (valore != null) {
            for (int i = 0; i < valore.length(); i++) {
                if (valore.charAt(i) > ' ') {
                    valoreHasContent = true;
                    break;
                }
            }
        }
        if (valore == null || !valoreHasContent) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.valore = valore;
    }
}
