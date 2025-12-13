package services;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

import java.sql.SQLException;
import java.util.ArrayList;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

@ExtendWith(MockitoExtension.class)
class RicercaServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private RicercaService searchService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RicercaService(null));
        assertTrue(exception.getMessage().contains("ProdottoDAO cannot be null"));
    }

    @Test
    @DisplayName("F2: Should instantiate service when ProdottoDAO is valid")
    void shouldInitializeSuccessfullyWhenDaoIsValid() {
        // Act & Assert
        assertNotNull(searchService);
    }

    // =================================================================================================
    // cercaProdotti Tests
    // =================================================================================================

    @ParameterizedTest
    @DisplayName("F1, F2, F3: Should throw exception when query is null or empty")
    @NullAndEmptySource
    void shouldThrowExceptionWhenQueryIsInvalid(String query) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> searchService.cercaProdotti(query));
        assertTrue(exception.getMessage().contains("Query string cannot be null or empty"));
    }

    @Test
    @DisplayName("F4: Should propagate exception when DAO fails")
    void shouldPropagateExceptionWhenDaoFails() throws SQLException {
        // Arrange
        when(prodottoDAO.cercaProdotti(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> searchService.cercaProdotti("valid"));
        assertEquals("Database error", exception.getMessage());
    }

    @Test
    @DisplayName("F5: Should return empty list when no matches are found")
    void shouldReturnEmptyListWhenNoMatches() throws SQLException {
        // Arrange
        String query = "unknown";
        when(prodottoDAO.cercaProdotti(anyString())).thenReturn(new ArrayList<>());

        // Act
        ArrayList<Prodotto> arrayProducts = searchService.cercaProdotti(query);

        // Assert
        assertAll("Should return empty list when no matches are found",
                () -> assertNotNull(arrayProducts),
                () -> assertTrue(arrayProducts.isEmpty()));
    }

    @Test
    @DisplayName("F6: Should return product list when matches are found")
    void shouldReturnProductsWhenMatchesFound() throws SQLException {
        // Arrange
        Prodotto product1 = new Prodotto();
        product1.setId(1);

        Prodotto product2 = new Prodotto();
        product2.setId(2);

        ArrayList<Prodotto> arrayProducts = new ArrayList<>();
        arrayProducts.add(product1);
        arrayProducts.add(product2);

        String query = "apple";

        when(prodottoDAO.cercaProdotti(query)).thenReturn(arrayProducts);

        // Act
        ArrayList<Prodotto> arrayRelevantProducts = searchService.cercaProdotti(query);

        // Assert
        assertAll("Should return product list when matches are found",
                () -> assertNotNull(arrayRelevantProducts),
                () -> assertEquals(2, arrayRelevantProducts.size()),
                () -> assertTrue(arrayRelevantProducts.contains(product1)),
                () -> assertTrue(arrayRelevantProducts.contains(product2)));
    }
}
