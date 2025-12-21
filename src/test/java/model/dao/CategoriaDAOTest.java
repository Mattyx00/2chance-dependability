package model.dao;

import model.beans.Categoria;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.MockedStatic;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class CategoriaDAOTest {

    private CategoriaDAO categoriaDAO;
    private MockedStatic<ConPool> mockedConPool;
    private Connection connection;
    private PreparedStatement preparedStatement;
    private ResultSet resultSet;

    @BeforeEach
    void setUp() throws SQLException {
        categoriaDAO = new CategoriaDAO();
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
    // Construction Tests
    // =================================================================================================

    @Test
    @DisplayName("Should instantiate DAO successfully")
    void shouldInstantiateDAO() {
        assertNotNull(categoriaDAO);
    }

    // =================================================================================================
    // getCategorie Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return empty list when database is empty")
    void shouldReturnEmptyListWhenDbIsEmpty() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false); // No rows

        // Act
        ArrayList<Categoria> result = categoriaDAO.getCategorie();

        // Assert
        assertTrue(result.isEmpty(), "Result list should be empty");
        verify(connection).prepareStatement("SELECT * FROM categoria");
    }

    @Test
    @DisplayName("F2: Should return all categories when database contains valid rows")
    void shouldReturnAllCategoriesWhenDbIsPopulated() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, true, false); // 2 rows then stop
        when(resultSet.getString(1)).thenReturn("Electronics", "Books");

        // Act
        ArrayList<Categoria> result = categoriaDAO.getCategorie();

        // Assert
        assertEquals(2, result.size());
        assertEquals("Electronics", result.get(0).getNomeCategoria());
        assertEquals("Books", result.get(1).getNomeCategoria());
    }

    @Test
    @DisplayName("F3: Should skip invalid entries when database contains invalid rows")
    void shouldSkipInvalidEntriesWhenDbHasInvalidRows() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        // Sequence: Valid("Valid"), Invalid(null), Invalid(""), Valid("AlsoValid"), End
        when(resultSet.next()).thenReturn(true, true, true, true, false);
        when(resultSet.getString(1)).thenReturn("Valid", null, "", "AlsoValid");

        // Act
        ArrayList<Categoria> result = categoriaDAO.getCategorie();

        // Assert
        assertEquals(2, result.size());
        assertEquals("Valid", result.get(0).getNomeCategoria());
        assertEquals("AlsoValid", result.get(1).getNomeCategoria());
    }

    @Test
    @DisplayName("F4: Should throw SQLException when database connection fails")
    void shouldThrowSQLExceptionWhenDbConnectionFails() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenThrow(new SQLException("DB Connection Failed"));

        // Act & Assert
        SQLException exception = assertThrows(SQLException.class, () -> categoriaDAO.getCategorie());
        assertEquals("DB Connection Failed", exception.getMessage());
    }

    // =================================================================================================
    // addCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("F5: Should throw exception when input Categoria is null")
    void shouldThrowExceptionWhenCategoriaIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> categoriaDAO.addCategoria(null));
        assertEquals("Il parametro 'categoria' non può essere null.", exception.getMessage());
    }

    @ParameterizedTest(name = "F6, F7, F8: Invalid name [{0}]")
    @CsvSource(value = {
            "NULL_VALUE", // Placeholder for null check logic inside test if needed, but CsvSource maps
                          // strings. using special handling strictly or separate test.
            "''",
            "'   '"
    }, nullValues = "NULL_VALUE")
    @DisplayName("F6-F8: Should throw exception when Categoria name is invalid")
    void shouldThrowExceptionWhenCategoriaNameIsInvalid(String invalidName) {
        // Arrange
        // We cannot use the real Categoria constructor for invalid names because it
        // throws exception itself!
        // The DAO checks: isValidCategoriaName(c.getNomeCategoria()).
        // If we create a Categoria, it enforces validation.
        // However, we are testing DAO's "defensive" check.
        // If Categoria bean throws exception on creation, we can't even pass it to DAO.
        // BUT, if we use a mock Categoria, we can spy/mock getNomeCategoria to return
        // invalid values.

        Categoria mockCategoria = mock(Categoria.class);
        when(mockCategoria.getNomeCategoria()).thenReturn(invalidName);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> categoriaDAO.addCategoria(mockCategoria));
        assertEquals("Il nome della categoria non può essere null o vuoto.", exception.getMessage());
    }

    @Test
    @DisplayName("F9: Should add category when input is valid")
    void shouldAddCategoriaWhenInputIsValid() throws SQLException {
        // Arrange
        Categoria c = new Categoria("NewCat");
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        int result = categoriaDAO.addCategoria(c);

        // Assert
        assertEquals(1, result);
        verify(connection).prepareStatement("INSERT INTO categoria VALUES (?)");
        verify(preparedStatement).setString(1, "NewCat");
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F10: Should throw SQLException when DB error occurs on add")
    void shouldThrowSQLExceptionWhenDbErrorOccursOnAdd() throws SQLException {
        // Arrange
        Categoria c = new Categoria("NewCat");
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenThrow(new SQLException("Insert failed"));

        // Act & Assert
        assertThrows(SQLException.class, () -> categoriaDAO.addCategoria(c));
    }

    // =================================================================================================
    // eliminaCategoria Tests
    // =================================================================================================

    @ParameterizedTest(name = "F11, F12, F13: Invalid name [{0}]")
    @CsvSource(value = { "NULL_VALUE", "''", "'   '" }, nullValues = "NULL_VALUE")
    @DisplayName("F11-F13: Should throw exception when name to delete is invalid")
    void shouldThrowExceptionWhenDeleteNameIsInvalid(String invalidName) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> categoriaDAO.eliminaCategoria(invalidName));
        assertTrue(exception.getMessage().contains("non può essere null o vuoto"));
    }

    @Test
    @DisplayName("F14: Should delete category when name exists")
    void shouldDeleteCategoriaWhenNameExists() throws SQLException {
        // Arrange
        String name = "ToDelete";
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        categoriaDAO.eliminaCategoria(name);

        // Assert
        verify(connection).prepareStatement("DELETE FROM categoria WHERE nome = ?");
        verify(preparedStatement).setString(1, name);
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F15: Should do nothing when name does not exist")
    void shouldDoNothingWhenDeleteNameDoesNotExist() throws SQLException {
        // Arrange
        // Even if it doesn't exist, executeUpdate returns 0 (or simply doesn't fail).
        // The requirement says "no exception".
        String name = "Ghost";
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(0);

        // Act
        categoriaDAO.eliminaCategoria(name);

        // Assert
        // Verify flow proceeded to executeUpdate but didn't throw
        verify(preparedStatement).executeUpdate();
    }
}
