package model.dao;

import model.beans.Specifiche;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class SpecificheDAO {

    private static final java.util.logging.Logger LOGGER = java.util.logging.Logger
            .getLogger(SpecificheDAO.class.getName());

    public SpecificheDAO() {
    }

    public ArrayList<Specifiche> getSpecificheByProd(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT nome, valore FROM specifiche WHERE id_prodotto = ?")) {
            stmt.setInt(1, id);
            LOGGER.info("Retrieving specifications for product ID: " + id);

            ArrayList<Specifiche> list = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    list.add(mapRowToSpecifiche(rs));
                }
            }
            return list;
        }
    }

    private Specifiche mapRowToSpecifiche(ResultSet rs) throws SQLException {
        Specifiche spec = new Specifiche();
        spec.setNome(rs.getString("nome"));
        spec.setValore(rs.getString("valore"));
        return spec;
    }
}
