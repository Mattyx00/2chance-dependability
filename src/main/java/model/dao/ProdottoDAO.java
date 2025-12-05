package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Specifiche;
import org.json.JSONArray;
import org.json.JSONObject;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class ProdottoDAO {

    public ProdottoDAO() {
    }

    public ArrayList<Prodotto> getProdotti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM prodotto WHERE disabilitato = 0")) {
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            ResultSet rs = stmt.executeQuery();

            while (rs.next()) {
                Prodotto p = new Prodotto();
                Categoria c = new Categoria();
                p.setId(rs.getInt(1));
                c.setNomeCategoria(rs.getString(2));
                p.setCategoria(c);
                p.setDescrizione(rs.getString(3));
                p.setDimensioni(rs.getString(4));
                p.setQuantitaProdotto(rs.getInt(5));
                p.setImmagine(rs.getString(7));
                p.setPeso(rs.getDouble(6));
                p.setMarca(rs.getString(8));
                p.setModello(rs.getString(9));
                p.setPrezzo(rs.getDouble(10));

                prodotti.add(p);
            }
            return prodotti;
        }
    }

    public Prodotto getProdottoById(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM prodotto WHERE id_prodotto = ? AND disabilitato = 0")) {
            stmt.setInt(1, idProdotto);
            ResultSet rs = stmt.executeQuery();

            if (rs.next()) {
                Prodotto p = new Prodotto();
                Categoria c = new Categoria();
                p.setId(rs.getInt(1));
                c.setNomeCategoria(rs.getString(2));
                p.setCategoria(c);
                p.setDescrizione(rs.getString(3));
                p.setDimensioni(rs.getString(4));
                p.setQuantitaProdotto(rs.getInt(5));
                p.setImmagine(rs.getString(7));
                p.setPeso(rs.getDouble(6));
                p.setMarca(rs.getString(8));
                p.setModello(rs.getString(9));
                p.setPrezzo(rs.getDouble(10));

                SpecificheDAO dao = new SpecificheDAO();
                p.setSpecifiche(dao.getSpecificheByProd(idProdotto));

                RecensioneDAO rdao = new RecensioneDAO();
                p.setRecensioni(rdao.getRecensioniByProdotto(p));

                return p;
            }
            return null;
        }
    }

    public ArrayList<Prodotto> getProdottiByCategoria(String categoria) throws SQLException {
        if (categoria == null || categoria.trim().isEmpty()) {
            throw new IllegalArgumentException("La categoria non può essere null o vuota");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM prodotto WHERE categoria = ? AND disabilitato = 0")) {
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            stmt.setString(1, categoria);
            ResultSet rs = stmt.executeQuery();

            while (rs.next()) {
                Prodotto p = new Prodotto();
                Categoria c = new Categoria();
                p.setId(rs.getInt(1));
                c.setNomeCategoria(rs.getString(2));
                p.setCategoria(c);
                p.setDescrizione(rs.getString(3));
                p.setDimensioni(rs.getString(4));
                p.setQuantitaProdotto(rs.getInt(5));
                p.setImmagine(rs.getString(7));
                p.setPeso(rs.getDouble(6));
                p.setMarca(rs.getString(8));
                p.setModello(rs.getString(9));
                p.setPrezzo(rs.getDouble(10));

                prodotti.add(p);
            }

            return prodotti;
        }
    }

    public int addProdotto(Prodotto p) throws SQLException {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "INSERT INTO prodotto VALUES (default, ?, ?, ?, ?, ?, ?, ?, ?, ?, default)")) {

            stmt.setString(1, p.getCategoria().getNomeCategoria());
            stmt.setString(2, p.getDescrizione());
            stmt.setString(3, p.getDimensioni());
            stmt.setInt(4, p.getQuantitaProdotto());
            stmt.setString(6, p.getImmagine());
            stmt.setDouble(5, p.getPeso());
            stmt.setString(7, p.getMarca());
            stmt.setString(8, p.getModello());
            System.out.println(p.getPrezzo());
            stmt.setDouble(9, p.getPrezzo());

            return stmt.executeUpdate();
        }
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM prodotto WHERE disabilitato = 0 ORDER BY id_prodotto DESC LIMIT 8")) {
            ArrayList<Prodotto> prodotti = new ArrayList<>();

            ResultSet rs = stmt.executeQuery();

            while (rs.next()) {
                Prodotto p = new Prodotto();
                Categoria c = new Categoria();
                p.setId(rs.getInt(1));
                c.setNomeCategoria(rs.getString(2));
                p.setCategoria(c);
                p.setDescrizione(rs.getString(3));
                p.setDimensioni(rs.getString(4));
                p.setQuantitaProdotto(rs.getInt(5));
                p.setImmagine(rs.getString(7));
                p.setPeso(rs.getDouble(6));
                p.setMarca(rs.getString(8));
                p.setModello(rs.getString(9));
                p.setPrezzo(rs.getDouble(10));

                prodotti.add(p);
            }

            return prodotti;
        }
    }

    public ArrayList<Prodotto> cercaProdotti(String nome) throws SQLException {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome di ricerca non può essere null o vuoto");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM prodotto WHERE UPPER(CONCAT(marca, modello, descrizione, categoria)) LIKE UPPER(?) AND disabilitato = 0")) {
            stmt.setString(1, nome);
            ResultSet rs = stmt.executeQuery();
            ArrayList<Prodotto> prodotti = new ArrayList<>();

            while (rs.next()) {
                Prodotto p = new Prodotto();
                Categoria c = new Categoria();
                p.setId(rs.getInt(1));
                c.setNomeCategoria(rs.getString(2));
                p.setCategoria(c);
                p.setDescrizione(rs.getString(3));
                p.setDimensioni(rs.getString(4));
                p.setQuantitaProdotto(rs.getInt(5));
                p.setImmagine(rs.getString(7));
                p.setPeso(rs.getDouble(6));
                p.setMarca(rs.getString(8));
                p.setModello(rs.getString(9));
                p.setPrezzo(rs.getDouble(10));

                prodotti.add(p);
            }
            return prodotti;
        }
    }

    public void eliminaProdotto(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("UPDATE prodotto SET disabilitato = 1 WHERE id_prodotto = ?")) {
            stmt.setInt(1, idProdotto);
            stmt.executeUpdate();
        }
    }

    public void aggiungiSpecifiche(ArrayList<Specifiche> specifiche, int idProdotto) throws SQLException {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null");
        }
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("INSERT INTO specifiche VALUES(?, ?, ?)")) {
            stmt.setInt(2, idProdotto);

            for (Specifiche s : specifiche) {
                stmt.setString(1, s.getNome());
                stmt.setString(3, s.getValore());
                stmt.executeUpdate();
            }
        }
    }

    public int getLastProduct() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT MAX(id_prodotto) FROM prodotto WHERE disabilitato = 0;")) {
            ResultSet rs = stmt.executeQuery();
            rs.next();

            return rs.getInt(1);
        }
    }

    public int eliminaSpecificheProdotto(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("DELETE FROM specifiche WHERE id_prodotto = ?")) {
            stmt.setInt(1, idProdotto);

            return stmt.executeUpdate();
        }
    }

    public void modificaProdotto(Prodotto p) throws SQLException {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        try (Connection connection = ConPool.getConnection()) {
            if (p.getImmagine() == null) {
                System.out.println("primo: " + p.getMarca() + " - " + p.getModello() + " " + p.getPrezzo() + " "
                        + p.getDescrizione() + " " + p.getDimensioni() + " " + p.getPeso() + " "
                        + p.getCategoria().getNomeCategoria() + " " + p.getId());
                try (PreparedStatement stmt = connection.prepareStatement(
                        "UPDATE prodotto SET marca = ?, modello = ?, prezzo = ?, descrizione = ?, dimensioni = ?, peso = ?, categoria = ? WHERE id_prodotto = ?")) {
                    stmt.setString(1, p.getMarca());
                    stmt.setString(2, p.getModello());
                    stmt.setDouble(3, p.getPrezzo());
                    stmt.setString(4, p.getDescrizione());
                    stmt.setString(5, p.getDimensioni());
                    stmt.setDouble(6, p.getPeso());
                    stmt.setString(7, p.getCategoria().getNomeCategoria());
                    stmt.setInt(8, p.getId());

                    stmt.executeUpdate();
                }
            }

            else {
                System.out.println("Secondo: " + p.getMarca() + " - " + p.getModello() + " " + p.getPrezzo() + " "
                        + p.getDescrizione() + " " + p.getDimensioni() + " " + p.getPeso() + " "
                        + p.getCategoria().getNomeCategoria() + " " + p.getId());
                try (PreparedStatement stmt = connection.prepareStatement(
                        "UPDATE prodotto SET marca = ?, modello = ?, prezzo = ?, descrizione = ?, dimensioni = ?, peso = ?, categoria = ?, immagine =? WHERE id_prodotto = ?")) {
                    stmt.setString(1, p.getMarca());
                    stmt.setString(2, p.getModello());
                    stmt.setDouble(3, p.getPrezzo());
                    stmt.setString(4, p.getDescrizione());
                    stmt.setString(5, p.getDimensioni());
                    stmt.setDouble(6, p.getPeso());
                    stmt.setString(7, p.getCategoria().getNomeCategoria());
                    stmt.setString(8, p.getImmagine());
                    stmt.setInt(9, p.getId());

                    stmt.executeUpdate();
                }
            }
        }
    }
}
