package model.dao;

import model.beans.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.MockedStatic;
import utils.ConPool;

import java.lang.reflect.Field;
import java.sql.*;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

class OrdineDAOTest {

    private OrdineDAO ordineDAO;
    private MockedStatic<ConPool> mockedConPool;
    private Connection connection;
    private PreparedStatement preparedStatement;
    private ResultSet resultSet;

    @BeforeEach
    void setUp() throws SQLException {
        ordineDAO = new OrdineDAO();
        connection = mock(Connection.class);
        preparedStatement = mock(PreparedStatement.class);
        resultSet = mock(ResultSet.class);

        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(connection);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // =================================================================================================
    // getOrdineById Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return populated Ordine when ID exists")
    void shouldReturnOrderWhenIdExists() throws SQLException {
        // Arrange
        int orderId = 10;
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true);
        when(resultSet.getInt("id_utente")).thenReturn(1);
        when(resultSet.getDate("data_ordine")).thenReturn(new java.sql.Date(System.currentTimeMillis()));
        when(resultSet.getString("indirizzo_spedizione")).thenReturn("Via Roma 1");
        when(resultSet.getDouble("prezzo_totale")).thenReturn(100.0);

        // Act
        Ordine result = ordineDAO.getOrdineById(orderId);

        // Assert
        assertEquals(orderId, result.getId());
        assertEquals("Via Roma 1", result.getIndirizzo());
        verify(connection).prepareStatement("SELECT * FROM ordine WHERE id_ordine = ?");
        verify(preparedStatement).setInt(1, orderId);
    }

    @Test
    @DisplayName("F2: Should return empty Ordine when ID does not exist")
    void shouldReturnEmptyOrderWhenIdDoesNotExist() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        Ordine result = ordineDAO.getOrdineById(999);

        // Assert
        assertEquals(0, result.getId());
        assertNull(result.getUtente());
    }

    @ParameterizedTest
    @CsvSource({ "0", "-1", "-100" })
    @DisplayName("F3, F4: Should throw exception when ID is invalid")
    void shouldThrowExceptionWhenIdIsInvalid(int id) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> ordineDAO.getOrdineById(id));
        assertTrue(exception.getMessage().contains("maggiore di zero"));
    }

    @Test
    @DisplayName("F5: Should throw SQLException when DB connection fails")
    void shouldThrowSQLExceptionWhenDbConnectionFails() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenThrow(new SQLException("Connection Error"));

        // Act & Assert
        assertThrows(SQLException.class, () -> ordineDAO.getOrdineById(1));
    }

    // =================================================================================================
    // getProdottoOrdine Tests
    // =================================================================================================

    @Test
    @DisplayName("F6: Should throw exception when Ordine is null")
    void shouldThrowExceptionWhenOrdineIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> ordineDAO.getProdottoOrdine(null));
        assertEquals("L'ordine non può essere null.", exception.getMessage());
    }

    @Test
    @DisplayName("F7: Should throw exception when Ordine ID is invalid")
    void shouldThrowExceptionWhenOrdineIdIsInvalid() {
        // Arrange
        Ordine o = new Ordine();
        o.setId(0);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> ordineDAO.getProdottoOrdine(o));
        assertTrue(exception.getMessage().contains("deve essere valido"));
    }

    @Test
    @DisplayName("F8: Should return populated Carrello when order has products")
    void shouldReturnCartWhenOrderHasProducts() throws SQLException {
        // Arrange
        Ordine o = new Ordine();
        o.setId(10);
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, false); // 2 items

        when(resultSet.getInt("quantita")).thenReturn(2, 1);
        when(resultSet.getInt(2)).thenReturn(101, 102);
        when(resultSet.getString(17)).thenReturn("BrandA", "BrandB");
        when(resultSet.getString(18)).thenReturn("ModelA", "ModelB"); // IMPORTANT: DAO reads this
        when(resultSet.getString(16)).thenReturn("imgA.jpg", "imgB.jpg");
        when(resultSet.getDouble(4)).thenReturn(50.0, 75.0);

        // Act
        Carrello result = ordineDAO.getProdottoOrdine(o);

        // Assert
        assertEquals(2, result.getProdotti().size());
        assertEquals(101, result.getProdotti().get(0).getProdotto().getId());
    }

    @Test
    @DisplayName("F9: Should return empty Carrello when order has no products")
    void shouldReturnEmptyCartWhenOrderHasNoProducts() throws SQLException {
        // Arrange
        Ordine o = new Ordine();
        o.setId(10);
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        Carrello result = ordineDAO.getProdottoOrdine(o);

        // Assert
        assertTrue(result.getProdotti().isEmpty());
    }

    // =================================================================================================
    // getOrdiniByUtente Tests
    // =================================================================================================

    @Test
    @DisplayName("F10: Should throw exception when Utente is null")
    void shouldThrowExceptionWhenUtenteIsNull() {
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.getOrdiniByUtente(null));
    }

    @Test
    @DisplayName("F11: Should throw exception when Utente ID is invalid")
    void shouldThrowExceptionWhenUtenteIdIsInvalid() {
        Utente u = new Utente();
        u.setId(0);
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.getOrdiniByUtente(u));
    }

    @Test
    @DisplayName("F12: Should return orders when user has history")
    void shouldReturnOrdersWhenUserHasHistory() throws SQLException {
        // Arrange
        Utente u = new Utente();
        u.setId(1);

        PreparedStatement stmtOrder = mock(PreparedStatement.class);
        ResultSet rsOrder = mock(ResultSet.class);

        when(connection.prepareStatement(contains("FROM ordine WHERE"))).thenReturn(stmtOrder);
        when(stmtOrder.executeQuery()).thenReturn(rsOrder);

        when(rsOrder.next()).thenReturn(true, false);
        when(rsOrder.getInt(1)).thenReturn(10);
        when(rsOrder.getInt(2)).thenReturn(1);
        when(rsOrder.getDate(3)).thenReturn(new java.sql.Date(System.currentTimeMillis()));
        when(rsOrder.getString(4)).thenReturn("Via Roma 1");
        when(rsOrder.getDouble(5)).thenReturn(100.0);

        PreparedStatement stmtItems = mock(PreparedStatement.class);
        ResultSet rsItems = mock(ResultSet.class);
        when(connection.prepareStatement(contains("FROM composto"))).thenReturn(stmtItems);
        when(stmtItems.executeQuery()).thenReturn(rsItems);
        when(rsItems.next()).thenReturn(false);

        // Act
        ArrayList<Ordine> result = ordineDAO.getOrdiniByUtente(u);

        // Assert
        assertEquals(1, result.size());
        assertEquals(10, result.get(0).getId());
    }

    @Test
    @DisplayName("F13: Should return empty list when user has no orders")
    void shouldReturnEmptyListWhenUserHasNoOrders() throws SQLException {
        // Arrange
        Utente u = new Utente();
        u.setId(1);
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        ArrayList<Ordine> result = ordineDAO.getOrdiniByUtente(u);

        // Assert
        assertTrue(result.isEmpty());
    }

    // =================================================================================================
    // addOrdine Tests
    // =================================================================================================

    private Ordine createValidOrder() {
        Ordine o = new Ordine();
        Utente u = new Utente();
        u.setId(1);
        o.setUtente(u);
        o.setIndirizzo("Via Valid");
        o.setPrezzoTotale(100.0);

        Carrello c = new Carrello();
        Prodotto p = new Prodotto();
        p.setId(5);
        p.setPrezzo(50.0);
        p.setMarca("Brand");
        p.setModello("Model");
        ProdottoCarrello pc = new ProdottoCarrello();
        pc.setProdotto(p);
        pc.setQuantita(2);
        c.aggiungiProdotto(pc);
        o.setCarrello(c);

        return o;
    }

    private static void setPrivateField(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to set field '" + fieldName + "' via reflection", e);
        }
    }

    @Test
    @DisplayName("F14: Should throw exception when Ordine is null")
    void shouldThrowExceptionWhenAddAndOrdineIsNull() {
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.addOrdine(null));
    }

    @Test
    @DisplayName("F15: Should throw exception when User is invalid")
    void shouldThrowExceptionWhenAddAndUserInvalid() {
        Ordine o = createValidOrder();
        o.getUtente().setId(0);
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.addOrdine(o));
    }

    @Test
    @DisplayName("F16: Should throw exception when Cart is empty")
    void shouldThrowExceptionWhenAddAndCartEmpty() {
        Ordine o = createValidOrder();
        o.setCarrello(new Carrello());
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.addOrdine(o));
    }

    @Test
    @DisplayName("F17: Should throw exception when Address is empty (DAO validation)")
    void shouldThrowExceptionWhenAddAndAddressEmpty() {
        // Arrange
        Ordine o = createValidOrder();

        // IMPORTANT: bypass Ordine.setIndirizzo validation to reach DAO validation
        setPrivateField(o, "indirizzo", "");

        // Act & Assert
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.addOrdine(o));
    }

    @Test
    @DisplayName("F18: Should throw exception when Product in cart is invalid")
    void shouldThrowExceptionWhenAddAndCartProductInvalid() throws SQLException {
        // Arrange
        Ordine o = createValidOrder();
        o.getCarrello().getProdotti().get(0).getProdotto().setId(0);

        when(connection.prepareStatement(anyString(), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        ResultSet generatedKeys = mock(ResultSet.class);
        when(preparedStatement.getGeneratedKeys()).thenReturn(generatedKeys);
        when(generatedKeys.next()).thenReturn(true);
        when(generatedKeys.getInt(1)).thenReturn(999);

        when(connection.prepareStatement(contains("INSERT INTO composto"))).thenReturn(preparedStatement);

        // Act & Assert
        assertThrows(IllegalArgumentException.class, () -> ordineDAO.addOrdine(o));
        verify(connection).rollback();
    }

    @Test
    @DisplayName("F19: Should create order successfully")
    void shouldCreateOrderSuccessfully() throws SQLException {
        // Arrange
        Ordine o = createValidOrder();

        PreparedStatement stmtOrder = mock(PreparedStatement.class);
        when(connection.prepareStatement(contains("INSERT INTO ordine"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(stmtOrder);
        when(stmtOrder.executeUpdate()).thenReturn(1);

        ResultSet generatedKeys = mock(ResultSet.class);
        when(stmtOrder.getGeneratedKeys()).thenReturn(generatedKeys);
        when(generatedKeys.next()).thenReturn(true);
        when(generatedKeys.getInt(1)).thenReturn(500);

        PreparedStatement stmtItems = mock(PreparedStatement.class);
        when(connection.prepareStatement(contains("INSERT INTO composto"))).thenReturn(stmtItems);
        when(stmtItems.executeUpdate()).thenReturn(1);

        // Act
        ordineDAO.addOrdine(o);

        // Assert
        verify(connection).setAutoCommit(false);
        verify(stmtOrder).executeUpdate();
        verify(stmtItems).executeUpdate();
        verify(connection).commit();
        verify(connection).setAutoCommit(true);
    }

    @Test
    @DisplayName("F20: Should rollback when item insertion fails")
    void shouldRollbackWhenItemInsertionFails() throws SQLException {
        // Arrange
        Ordine o = createValidOrder();

        PreparedStatement stmtOrder = mock(PreparedStatement.class);
        when(connection.prepareStatement(contains("INSERT INTO ordine"), eq(Statement.RETURN_GENERATED_KEYS)))
                .thenReturn(stmtOrder);
        when(stmtOrder.executeUpdate()).thenReturn(1);

        ResultSet generatedKeys = mock(ResultSet.class);
        when(stmtOrder.getGeneratedKeys()).thenReturn(generatedKeys);
        when(generatedKeys.next()).thenReturn(true);
        when(generatedKeys.getInt(1)).thenReturn(500);

        PreparedStatement stmtItems = mock(PreparedStatement.class);
        when(connection.prepareStatement(contains("INSERT INTO composto"))).thenReturn(stmtItems);
        when(stmtItems.executeUpdate()).thenThrow(new SQLException("Item duplicate"));

        // Act & Assert
        assertThrows(SQLException.class, () -> ordineDAO.addOrdine(o));
        verify(connection).rollback();
        verify(connection, never()).commit();
    }

    // =================================================================================================
    // getOrdini Tests
    // =================================================================================================

    @Test
    @DisplayName("F21: Should return empty list when no orders exist")
    void shouldReturnEmptyListWhenNoOrdersExist() throws SQLException {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        ArrayList<Ordine> result = ordineDAO.getOrdini();
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("F22: Should return list of all orders")
    void shouldReturnListOfAllOrders() throws SQLException {
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, false);

        when(resultSet.getInt(1)).thenReturn(1, 2);
        when(resultSet.getInt(2)).thenReturn(10, 20);
        when(resultSet.getDate(3)).thenReturn(new java.sql.Date(System.currentTimeMillis()),
                new java.sql.Date(System.currentTimeMillis()));
        when(resultSet.getString(4)).thenReturn("Via 1", "Via 2");
        when(resultSet.getDouble(5)).thenReturn(10.0, 20.0);

        ArrayList<Ordine> result = ordineDAO.getOrdini();
        assertEquals(2, result.size());
    }
}
