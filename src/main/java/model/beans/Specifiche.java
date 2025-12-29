package model.beans;

public class Specifiche {

    /*@ spec_public nullable @*/
    private String nome, valore;

    /*@
      @ assignable \nothing;
      @ ensures this.nome == null;
      @ ensures this.valore == null;
      @*/
    public Specifiche() {
        super();
    }

    /*@
      @ public normal_behavior
      @   requires nome != null && !nome.trim().isEmpty();
      @   requires valore != null && !valore.trim().isEmpty();
      @   assignable this.nome, this.valore;
      @   ensures this.nome == nome;
      @   ensures this.valore == valore;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires (nome == null || nome.trim().isEmpty()) || (valore == null || valore.trim().isEmpty());
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public Specifiche(String nome, String valore) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        if (valore == null || valore.trim().isEmpty()) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.nome = nome;
        this.valore = valore;
    }

    /*@
      @ ensures \result == this.nome;
      @ pure
      @*/
    public String getNome() {
        return nome;
    }

    /*@
      @ public normal_behavior
      @   requires nome != null && !nome.trim().isEmpty();
      @   assignable this.nome;
      @   ensures this.nome == nome;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires nome == null || nome.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setNome(String nome) {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della specifica non può essere null o vuoto");
        }
        this.nome = nome;
    }

    /*@
      @ ensures \result == this.valore;
      @ pure
      @*/
    public String getValore() {
        return valore;
    }

    /*@
      @ public normal_behavior
      @   requires valore != null && !valore.trim().isEmpty();
      @   assignable this.valore;
      @   ensures this.valore == valore;
      @
      @ also
      @
      @ public exceptional_behavior
      @   requires valore == null || valore.trim().isEmpty();
      @   assignable \nothing;
      @   signals (IllegalArgumentException e) true;
      @*/
    public void setValore(String valore) {
        if (valore == null || valore.trim().isEmpty()) {
            throw new IllegalArgumentException("Il valore della specifica non può essere null o vuoto");
        }
        this.valore = valore;
    }
}
