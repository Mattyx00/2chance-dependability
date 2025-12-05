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
    public SpecificheDAO() {
    }

    public ArrayList<Specifiche> getSpecificheByProd(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT nome, valore FROM specifiche WHERE id_prodotto = ?")) {
            stmt.setInt(1, id);
            ArrayList<Specifiche> list = new ArrayList<>();
            ResultSet rs = stmt.executeQuery();

            while (rs.next()) {
                Specifiche spec = new Specifiche();

                spec.setNome(rs.getString(1));
                spec.setValore(rs.getString(2));
                list.add(spec);
            }

            return list;
        }
    }
}
