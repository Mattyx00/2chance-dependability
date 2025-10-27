package model.dao;

import model.beans.Prodotto;
import model.beans.Specifiche;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class SpecificheDAO {
    private Connection connection;
    public SpecificheDAO() throws SQLException {
        connection = ConPool.getConnection();
    }

    public ArrayList<Specifiche> getSpecificheByProd (int id) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT nome, valore FROM specifiche WHERE id_prodotto = ?");
        stmt.setInt(1, id);
        ArrayList<Specifiche> list = new ArrayList<>();
        ResultSet rs = stmt.executeQuery();

        while(rs.next()){
            Specifiche spec = new Specifiche();

            spec.setNome(rs.getString(1));
            spec.setValore(rs.getString(2));
            list.add(spec);
        }

        return list;
    }
}

