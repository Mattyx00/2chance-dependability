package model.dao;

import model.beans.Specifiche;
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
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class SpecificheDAOTest {

    private SpecificheDAO specificheDAO;
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
        specificheDAO = new SpecificheDAO();
        conPoolMock = mockStatic(ConPool.class);
        conPoolMock.when(ConPool::getConnection).thenReturn(connection);
    }

    @AfterEach
    void tearDown() {
        conPoolMock.close();
    }

    // =================================================================================================
    // getSpecificheByProd Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return specifiche list when product ID is valid and specs exist")
    void shouldReturnSpecificheListWhenProductIdIsValidAndSpecsExist() throws SQLException {
        // Arrange
        int validId = 1;
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);

        // Simulate one result
        when(resultSet.next()).thenReturn(true, false);
        when(resultSet.getString("nome")).thenReturn("Colore");
        when(resultSet.getString("valore")).thenReturn("Rosso");

        // Act
        ArrayList<Specifiche> result = specificheDAO.getSpecificheByProd(validId);

        // Assert
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals("Colore", result.get(0).getNome());
        assertEquals("Rosso", result.get(0).getValore());
        verify(preparedStatement).setInt(1, validId);
    }

    @Test
    @DisplayName("F2: Should return empty list when product ID is valid but no specs exist")
    void shouldReturnEmptyListWhenProductIdIsValidButNoSpecsExist() throws SQLException {
        // Arrange
        int validId = 100;
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        ArrayList<Specifiche> result = specificheDAO.getSpecificheByProd(validId);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @ParameterizedTest
    @DisplayName("F3, F4: Should throw exception when Product ID is invalid")
    @CsvSource({
            "0",
            "-1",
            "-100"
    })
    void shouldThrowExceptionWhenProductIdIsInvalid(int invalidId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> specificheDAO.getSpecificheByProd(invalidId));
        assertEquals("L'ID del prodotto deve essere maggiore di zero.", exception.getMessage());
    }
}
