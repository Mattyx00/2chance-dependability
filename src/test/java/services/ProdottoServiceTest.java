package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class ProdottoServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private ProdottoService prodottoService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("C2: Should instantiate service when ProdottoDAO is non-null")
    void shouldInitializeSuccessfullyWhenProdottoDAOIsValid() {
        // Act & Assert
        assertNotNull(prodottoService);
    }

    @Test
    @DisplayName("C1: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottoService(null));
        assertTrue(exception.getMessage().contains("ProdottoDAO cannot be null"));
    }

    // =================================================================================================
    // getProdottoById Tests
    // =================================================================================================

    @ParameterizedTest(name = "G1, G2: Should throw exception when id is {0}")
    @ValueSource(ints = { 0, -1, -100 })
    @DisplayName("G1, G2: Should throw exception when ID is invalid")
    void shouldThrowExceptionWhenIdIsInvalid(int invalidId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> prodottoService.getProdottoById(invalidId));
        assertTrue(exception.getMessage().contains("Product ID must be greater than 0"));
    }

    @Test
    @DisplayName("G3: Should return product when product is found")
    void shouldReturnProductWhenFound() throws SQLException {
        // Arrange
        int productId = 1;
        Prodotto expectedProdotto = new Prodotto();
        expectedProdotto.setId(productId);

        when(prodottoDAO.getProdottoById(productId)).thenReturn(expectedProdotto);

        // Act
        Prodotto actualProdotto = prodottoService.getProdottoById(productId);

        // Assert
        assertAll(
                () -> assertNotNull(actualProdotto),
                () -> assertEquals(expectedProdotto, actualProdotto));
        verify(prodottoDAO).getProdottoById(productId);
    }

    @Test
    @DisplayName("G4: Should return null when product is not found")
    void shouldReturnNullWhenProductNotFound() throws SQLException {
        // Arrange
        int productId = 1;
        when(prodottoDAO.getProdottoById(productId)).thenReturn(null);

        // Act
        Prodotto product = prodottoService.getProdottoById(productId);

        // Assert
        assertNull(product);

        verify(prodottoDAO).getProdottoById(productId);
    }

    @Test
    @DisplayName("G5: Should propagate SQLException when DAO throws exception")
    void shouldPropagateSQLException() throws SQLException {
        // Arrange
        int productId = 1;

        when(prodottoDAO.getProdottoById(productId)).thenThrow(new SQLException("Database Error"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> prodottoService.getProdottoById(productId));
        assertEquals("Database Error", exception.getMessage());

        verify(prodottoDAO).getProdottoById(productId);
    }
}
