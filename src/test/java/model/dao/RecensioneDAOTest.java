package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.Mock;
import org.mockito.MockedStatic;
import org.mockito.MockitoAnnotations;
import utils.ConPool;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class RecensioneDAOTest {

    private RecensioneDAO recensioneDAO;
    private MockedStatic<ConPool> conPoolMock;

    @Mock
    private Connection connection;

    @Mock
    private PreparedStatement preparedStatement;

    @Mock
    private ResultSet resultSet;

    @BeforeEach
    void setUp() throws SQLException {
        MockitoAnnotations.openMocks(this);
        recensioneDAO = new RecensioneDAO();
        conPoolMock = mockStatic(ConPool.class);
        conPoolMock.when(ConPool::getConnection).thenReturn(connection);
    }

    @AfterEach
    void tearDown() {
        conPoolMock.close();
    }

    // =================================================================================================
    // getRecensioniByUtente Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return review list when user is valid and reviews exist")
    void shouldReturnReviewListWhenUserIsValidAndReviewsExist() throws SQLException {
        // Arrange
        Utente user = new Utente();
        user.setId(1);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        // Simulate one result
        when(resultSet.next()).thenReturn(true, false);
        mockResultSetRow(resultSet);

        // Act
        ArrayList<Recensione> result = recensioneDAO.getRecensioniByUtente(user);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(1, result.get(0).getId());
        assertEquals(1, result.get(0).getUtente().getId());
        verify(preparedStatement).setInt(1, 1);
    }

    @Test
    @DisplayName("F2: Should return empty list when user is valid but no reviews exist")
    void shouldReturnEmptyListWhenUserIsValidButNoReviewsExist() throws SQLException {
        // Arrange
        Utente user = new Utente();
        user.setId(1);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        ArrayList<Recensione> result = recensioneDAO.getRecensioniByUtente(user);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("F3: Should throw exception when User is null")
    void shouldThrowExceptionWhenUserIsNull() {
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.getRecensioniByUtente(null));
    }

    @Test
    @DisplayName("F4: Should throw exception when User ID is invalid")
    void shouldThrowExceptionWhenUserIdIsInvalid() {
        Utente user = new Utente();
        user.setId(0); // Invalid
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.getRecensioniByUtente(user));
    }

    // =================================================================================================
    // getRecensioniByProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("F5: Should return review list when product is valid and reviews exist")
    void shouldReturnReviewListWhenProductIsValidAndReviewsExist() throws SQLException {
        // Arrange
        Prodotto product = new Prodotto();
        product.setId(10);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, false);
        mockResultSetRow(resultSet);

        // Act
        ArrayList<Recensione> result = recensioneDAO.getRecensioniByProdotto(product);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(1, result.get(0).getId());
    }

    @Test
    @DisplayName("F6: Should return empty list when product is valid but no reviews exist")
    void shouldReturnEmptyListWhenProductIsValidButNoReviewsExist() throws SQLException {
        // Arrange
        Prodotto product = new Prodotto();
        product.setId(10);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        ArrayList<Recensione> result = recensioneDAO.getRecensioniByProdotto(product);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("F7: Should throw exception when Product is null")
    void shouldThrowExceptionWhenProductIsNull() {
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.getRecensioniByProdotto(null));
    }

    @Test
    @DisplayName("F8: Should throw exception when Product ID is invalid")
    void shouldThrowExceptionWhenProductIdIsInvalid() {
        Prodotto product = new Prodotto();
        product.setId(-1);
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.getRecensioniByProdotto(product));
    }

    // =================================================================================================
    // addRecensione Tests
    // =================================================================================================

    @Test
    @DisplayName("F9: Should add review when all fields are valid")
    void shouldAddReviewWhenAllFieldsAreValid() throws SQLException {
        // Arrange
        Recensione recensione = createValidRecensioneMock(); // Use Mock
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        int result = recensioneDAO.addRecensione(recensione);

        // Assert
        assertEquals(1, result);
        verify(preparedStatement).setInt(1, recensione.getUtente().getId());
        verify(preparedStatement).setInt(2, recensione.getProdotto().getId());
        verify(preparedStatement).setString(3, recensione.getTesto());
        verify(preparedStatement).setInt(4, recensione.getValutazione());
    }

    @Test
    @DisplayName("F10: Should throw exception when Recensione is null")
    void shouldThrowExceptionWhenRecensioneIsNull() {
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(null));
    }

    @Test
    @DisplayName("F11: Should throw exception when nested User is invalid")
    void shouldThrowExceptionWhenNestedUserIsInvalid() {
        Recensione r = mock(Recensione.class);
        when(r.getProdotto()).thenReturn(new Prodotto());
        when(r.getUtente()).thenReturn(null);
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));

        Utente u = mock(Utente.class);
        when(u.getId()).thenReturn(0);
        when(r.getUtente()).thenReturn(u);
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));
    }

    @Test
    @DisplayName("F12: Should throw exception when nested Product is invalid")
    void shouldThrowExceptionWhenNestedProductIsInvalid() {
        Recensione r = mock(Recensione.class);
        Utente u = mock(Utente.class);
        when(u.getId()).thenReturn(1);
        when(r.getUtente()).thenReturn(u);

        when(r.getProdotto()).thenReturn(null);
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));

        Prodotto p = mock(Prodotto.class);
        when(p.getId()).thenReturn(0);
        when(r.getProdotto()).thenReturn(p);
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));
    }

    @ParameterizedTest
    @DisplayName("F13: Should throw exception when Text is invalid")
    @CsvSource({
            "null_text",
            "empty",
            "blank"
    })
    void shouldThrowExceptionWhenTextIsInvalid(String scenario) {
        Recensione r = mock(Recensione.class);
        Utente u = mock(Utente.class);
        when(u.getId()).thenReturn(1);
        when(r.getUtente()).thenReturn(u);
        Prodotto p = mock(Prodotto.class);
        when(p.getId()).thenReturn(1);
        when(r.getProdotto()).thenReturn(p);

        String invalidText = null;
        if ("empty".equals(scenario))
            invalidText = "";
        if ("blank".equals(scenario))
            invalidText = "   ";

        when(r.getTesto()).thenReturn(invalidText);

        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));
    }

    @ParameterizedTest
    @DisplayName("F14, F15: Should throw exception when Rating is invalid")
    @CsvSource({
            "0",
            "6",
            "-1",
            "10"
    })
    void shouldThrowExceptionWhenRatingIsInvalid(int invalidRating) {
        Recensione r = mock(Recensione.class);
        Utente u = mock(Utente.class);
        when(u.getId()).thenReturn(1);
        when(r.getUtente()).thenReturn(u);
        Prodotto p = mock(Prodotto.class);
        when(p.getId()).thenReturn(1);
        when(r.getProdotto()).thenReturn(p);
        when(r.getTesto()).thenReturn("Valid Text");

        when(r.getValutazione()).thenReturn(invalidRating);

        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.addRecensione(r));
    }

    // =================================================================================================
    // deleteRecensione Tests
    // =================================================================================================

    @Test
    @DisplayName("F16: Should delete review when ID is valid")
    void shouldDeleteReviewWhenIdIsValid() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        recensioneDAO.deleteRecensione(5);

        // Assert
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F17: Should throw exception when ID is invalid")
    void shouldThrowExceptionWhenDeleteIdIsInvalid() {
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.deleteRecensione(0));
        assertThrows(IllegalArgumentException.class, () -> recensioneDAO.deleteRecensione(-10));
    }

    // =================================================================================================
    // Helpers
    // =================================================================================================

    private Recensione createValidRecensioneMock() {
        Recensione r = mock(Recensione.class);
        Utente u = mock(Utente.class);
        when(u.getId()).thenReturn(1);

        Prodotto p = mock(Prodotto.class);
        when(p.getId()).thenReturn(10);

        when(r.getUtente()).thenReturn(u);
        when(r.getProdotto()).thenReturn(p);
        when(r.getTesto()).thenReturn("Valid Text");
        when(r.getValutazione()).thenReturn(5);

        return r;
    }

    private void mockResultSetRow(ResultSet rs) throws SQLException {
        // 1: Recensione ID
        when(rs.getInt(1)).thenReturn(1);
        // 2: Utente ID
        when(rs.getInt(2)).thenReturn(1);
        // 3: Prodotto ID
        when(rs.getInt(3)).thenReturn(10);
        // 4: Data Recensione
        when(rs.getDate(4)).thenReturn(new Date(System.currentTimeMillis()));
        // 5: Testo
        when(rs.getString(5)).thenReturn("Ottimo prodotto");
        // 6: Valutazione
        when(rs.getInt(6)).thenReturn(5);

        // Additional columns used in mapping
        // 8: Utente Nome
        when(rs.getString(8)).thenReturn("Mario");
        // 9: Utente Cognome
        when(rs.getString(9)).thenReturn("Rossi");
        // 10: Utente Admin
        when(rs.getBoolean(10)).thenReturn(false);
        // 11: Email
        when(rs.getString(11)).thenReturn("test@test.com");
        // 12: Telefono
        when(rs.getString(12)).thenReturn("1234567890");
        // 13: Password
        when(rs.getString(13)).thenReturn("pass");
        // 14: Immagine
        when(rs.getString(14)).thenReturn("img.jpg");

        // 16: Categoria Nome
        when(rs.getString(16)).thenReturn("Elettronica");
        // 17: Descrizione
        when(rs.getString(17)).thenReturn("Descrizione");
        // 18: Dimensioni
        when(rs.getString(18)).thenReturn("10x10");
        // 19: Quantita
        when(rs.getInt(19)).thenReturn(5);
        // 20: Peso
        when(rs.getDouble(20)).thenReturn(1.5);
        // 21: Immagine Prod
        when(rs.getString(21)).thenReturn("prod.jpg");
        // 22: Marca
        when(rs.getString(22)).thenReturn("Brand");
        // 23: Modello
        when(rs.getString(23)).thenReturn("Model");
        // 24: Prezzo
        when(rs.getDouble(24)).thenReturn(99.99);
    }
}
