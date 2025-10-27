package model.dao;

import model.beans.Categoria;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class CategoriaDAO {

    private Connection connection;

    public CategoriaDAO() throws SQLException {
        this.connection = ConPool.getConnection();
    }

    public ArrayList<Categoria> getCategorie() throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT * FROM categoria");
        ArrayList<Categoria> categorie = new ArrayList<>();
        ResultSet set = stmt.executeQuery();


        while(set.next()){
            Categoria c = new Categoria();
            c.setNomeCategoria(set.getString(1));
            categorie.add(c);
        }
        return categorie;
    }

    public int addCategoria(Categoria c) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("INSERT INTO categoria VALUES (?)");
        stmt.setString(1, c.getNomeCategoria());
        return stmt.executeUpdate();

    }

    public void eliminaCategoria(String nome) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("DELETE FROM categoria WHERE nome = ?");
        stmt.setString(1, nome);

        stmt.executeUpdate();
    }

}
