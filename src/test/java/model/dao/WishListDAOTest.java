package model.dao;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
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
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class WishListDAOTest {

    private WishListDAO wishListDAO;
    private MockedStatic<ConPool> conPoolMock;

    @Mock
    private Connection connection;

    @Mock
    private PreparedStatement preparedStatement;

    @Mock
    private ResultSet resultSet;

    @Mock
    private ProdottoDAO prodottoDAO;

    @BeforeEach
    void setUp() throws SQLException {
        MockitoAnnotations.openMocks(this);

        // Spy on WishListDAO to mock protected factory method
        wishListDAO = spy(new WishListDAO());
        doReturn(prodottoDAO).when(wishListDAO).getProdottoDAO();

        conPoolMock = mockStatic(ConPool.class);
        conPoolMock.when(ConPool::getConnection).thenReturn(connection);

        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
    }

    @AfterEach
    void tearDown() {
        conPoolMock.close();
    }

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should instantiate successfully")
    void shouldInstantiateSuccessfully() {
        // Act
        WishListDAO dao = new WishListDAO();

        // Assert
        assertNotNull(dao);
    }

    // =================================================================================================
    // addToWishList Tests (F2-F9)
    // =================================================================================================

    @Test
    @DisplayName("F2: Should add to wishlist when inputs valid")
    void shouldAddToWishListWhenInputsValid() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        Prodotto prodotto = createValidProdotto(2);

        // Act
        wishListDAO.addToWishList(utente, prodotto);

        // Assert
        verify(preparedStatement).setInt(1, 1);
        verify(preparedStatement).setInt(2, 2);
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F3: Should throw exception when Utente is null")
    void shouldThrowExceptionWhenUtenteIsNull() {
        // Arrange
        Prodotto prodotto = createValidProdotto(2);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.addToWishList(null, prodotto));
        assertEquals("L'utente non può essere null.", exception.getMessage());
    }

    @Test
    @DisplayName("F4: Should throw exception when Prodotto is null")
    void shouldThrowExceptionWhenProdottoIsNull() {
        // Arrange
        Utente utente = createValidUtente(1);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.addToWishList(utente, null));
        assertEquals("Il prodotto non può essere null.", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("F5, F7: Should throw exception when Utente ID is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowExceptionWhenUtenteIdIsInvalid(int invalidId) {
        // Arrange
        Utente utente = createValidUtente(invalidId);
        Prodotto prodotto = createValidProdotto(2);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.addToWishList(utente, prodotto));
        assertEquals("L'ID dell'utente deve essere maggiore di zero.", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("F6, F8: Should throw exception when Prodotto ID is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowExceptionWhenProdottoIdIsInvalid(int invalidId) {
        // Arrange
        Utente utente = createValidUtente(1);
        Prodotto prodotto = createValidProdotto(invalidId);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.addToWishList(utente, prodotto));
        assertEquals("L'ID del prodotto deve essere maggiore di zero.", exception.getMessage());
    }

    @Test
    @DisplayName("F9: Should throw SQLException on duplicate entry")
    void shouldThrowSQLExceptionOnDuplicateEntry() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        Prodotto prodotto = createValidProdotto(2);
        when(preparedStatement.executeUpdate()).thenThrow(new SQLException("Duplicate entry"));

        // Act & Assert
        assertThrows(SQLException.class, () -> wishListDAO.addToWishList(utente, prodotto));
    }

    // =================================================================================================
    // getWishListByUser Tests (F10-F16)
    // =================================================================================================

    @Test
    @DisplayName("F10: Should return WishList with products when user valid")
    void shouldReturnWishListWithProductsWhenUserValid() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, false);
        when(resultSet.getInt(2)).thenReturn(10, 20);

        Prodotto p1 = createValidProdotto(10);
        Prodotto p2 = createValidProdotto(20);
        when(prodottoDAO.getProdottoById(10)).thenReturn(p1);
        when(prodottoDAO.getProdottoById(20)).thenReturn(p2);

        // Act
        WishList result = wishListDAO.getWishListByUser(utente);

        // Assert
        assertNotNull(result);
        assertEquals(utente, result.getUtente());
        assertEquals(2, result.getProdotti().size());
        assertTrue(result.getProdotti().contains(p1));
        assertTrue(result.getProdotti().contains(p2));
    }

    @Test
    @DisplayName("F11: Should return empty WishList when no entries")
    void shouldReturnEmptyWishListWhenNoEntries() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        WishList result = wishListDAO.getWishListByUser(utente);

        // Assert
        assertNotNull(result);
        assertEquals(utente, result.getUtente());
        assertTrue(result.getProdotti().isEmpty());
    }

    @Test
    @DisplayName("F12: Should throw exception when Utente is null")
    void shouldThrowExceptionWhenUtenteIsNullInGetWishList() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.getWishListByUser(null));
        assertEquals("L'utente non può essere null.", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("F13, F14: Should throw exception when Utente ID is invalid")
    @CsvSource({ "0", "-5", "-100" })
    void shouldThrowExceptionWhenUtenteIdIsInvalidInGetWishList(int invalidId) {
        // Arrange
        Utente utente = createValidUtente(invalidId);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.getWishListByUser(utente));
        assertEquals("L'ID dell'utente deve essere maggiore di zero.", exception.getMessage());
    }

    @Test
    @DisplayName("F15: Should handle product load failure gracefully")
    void shouldHandleProductLoadFailureGracefully() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, false);
        when(resultSet.getInt(2)).thenReturn(10, 20);

        when(prodottoDAO.getProdottoById(10)).thenThrow(new SQLException("DB Error"));
        Prodotto p2 = createValidProdotto(20);
        when(prodottoDAO.getProdottoById(20)).thenReturn(p2);

        // Act
        WishList result = wishListDAO.getWishListByUser(utente);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.getProdotti().size());
        assertEquals(p2, result.getProdotti().get(0));
    }

    @Test
    @DisplayName("F16: Should skip invalid product IDs from database")
    void shouldSkipInvalidProductIdsFromDatabase() throws SQLException {
        // Arrange
        Utente utente = createValidUtente(1);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, true, false);
        when(resultSet.getInt(2)).thenReturn(0, -5, 30);

        Prodotto p3 = createValidProdotto(30);
        when(prodottoDAO.getProdottoById(30)).thenReturn(p3);

        // Act
        WishList result = wishListDAO.getWishListByUser(utente);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.getProdotti().size());
        assertEquals(p3, result.getProdotti().get(0));
    }

    // =================================================================================================
    // removeFromWishList Tests (F17-F22)
    // =================================================================================================

    @Test
    @DisplayName("F17: Should remove from wishlist when entry exists")
    void shouldRemoveFromWishListWhenEntryExists() throws SQLException {
        // Arrange
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        wishListDAO.removeFromWishList(1, 2);

        // Assert
        verify(preparedStatement).setInt(1, 1);
        verify(preparedStatement).setInt(2, 2);
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F18: Should handle non-existent entry gracefully")
    void shouldHandleNonExistentEntryGracefully() throws SQLException {
        // Arrange
        when(preparedStatement.executeUpdate()).thenReturn(0);

        // Act
        wishListDAO.removeFromWishList(1, 999);

        // Assert
        verify(preparedStatement).executeUpdate();
    }

    @ParameterizedTest
    @DisplayName("F19, F21: Should throw exception when user ID is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowExceptionWhenUserIdIsInvalidInRemove(int invalidId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.removeFromWishList(invalidId, 5));
        assertEquals("L'ID dell'utente deve essere maggiore di zero.", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("F20, F22: Should throw exception when product ID is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowExceptionWhenProductIdIsInvalidInRemove(int invalidId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishListDAO.removeFromWishList(5, invalidId));
        assertEquals("L'ID del prodotto deve essere maggiore di zero.", exception.getMessage());
    }

    // =================================================================================================
    // Helpers
    // =================================================================================================

    private Utente createValidUtente(int id) {
        Utente u = new Utente();
        u.setId(id);
        u.setNome("Nome");
        u.setCognome("Cognome");
        u.setEmail("test@test.com");
        u.setPassword("password");
        return u;
    }

    private Prodotto createValidProdotto(int id) {
        Prodotto p = new Prodotto();
        p.setId(id);
        p.setMarca("Marca");
        p.setModello("Modello");
        p.setPrezzo(100.0);
        return p;
    }
}
