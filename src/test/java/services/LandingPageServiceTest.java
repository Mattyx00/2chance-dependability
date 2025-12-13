package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assumptions.abort;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class LandingPageServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private LandingPageService landingPageService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should instantiate service with default constructor")
    void shouldInitializeWithDefaultConstructor() {
        // Act & Assert
        assertDoesNotThrow(() -> {
            try {
                new LandingPageService();
            } catch (SQLException e) {
                abort("Skipping test: Database connection failed - " + e.getMessage());
            }
        });
    }

    @Test
    @DisplayName("F2: Should instantiate service when valid ProdottoDAO is provided")
    void shouldInitializeWhenDaoIsNotNull() {
        // Act
        LandingPageService service = new LandingPageService(prodottoDAO);

        // Assert
        assertNotNull(service);
    }

    @Test
    @DisplayName("F3: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new LandingPageService(null));
        assertEquals("ProdottoDAO cannot be null", exception.getMessage());
    }

    // =================================================================================================
    // getUltimiProdotti Tests
    // =================================================================================================

    @Test
    @DisplayName("F4: Should return product list when DAO returns products")
    void shouldReturnProductListWhenDaoReturnsProducts() throws SQLException {
        // Arrange
        Prodotto product1 = new Prodotto();
        product1.setId(1);

        Prodotto product2 = new Prodotto();
        product2.setId(2);

        ArrayList<Prodotto> expectedProducts = new ArrayList<>(Arrays.asList(product1, product2));

        when(prodottoDAO.getUltimiProdotti()).thenReturn(expectedProducts);

        // Act
        ArrayList<Prodotto> actualProducts = landingPageService.getUltimiProdotti();

        // Assert
        assertEquals(expectedProducts, actualProducts);

        verify(prodottoDAO).getUltimiProdotti();
    }

    @Test
    @DisplayName("F5: Should return empty list when DAO returns empty list")
    void shouldReturnEmptyListWhenDaoReturnsEmpty() throws SQLException {
        // Arrange
        ArrayList<Prodotto> expectedEmptyArrayProducts = new ArrayList<>();

        when(prodottoDAO.getUltimiProdotti()).thenReturn(expectedEmptyArrayProducts);

        // Act
        ArrayList<Prodotto> actualEmptyArrayProducts = landingPageService.getUltimiProdotti();

        // Assert
        assertAll(
                () -> assertTrue(actualEmptyArrayProducts.isEmpty()),
                () -> assertEquals(expectedEmptyArrayProducts, actualEmptyArrayProducts));

        verify(prodottoDAO).getUltimiProdotti();
    }

    @Test
    @DisplayName("F6: Should return empty list when DAO returns null")
    void shouldReturnEmptyListWhenDaoReturnsNull() throws SQLException {
        // Arrange
        when(prodottoDAO.getUltimiProdotti()).thenReturn(null);

        // Act
        ArrayList<Prodotto> emptyArrayProducts = landingPageService.getUltimiProdotti();

        // Assert
        assertAll(
                () -> assertNotNull(emptyArrayProducts),
                () -> assertTrue(emptyArrayProducts.isEmpty()));

        verify(prodottoDAO).getUltimiProdotti();
    }

    @Test
    @DisplayName("F7: Should propagate SQLException when DAO fails")
    void shouldPropagateSqlExceptionWhenDaoFails() throws SQLException {
        // Arrange
        when(prodottoDAO.getUltimiProdotti()).thenThrow(new SQLException("Database error"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> landingPageService.getUltimiProdotti());
        assertEquals("Database error", exception.getMessage());

        verify(prodottoDAO).getUltimiProdotti();
    }
}
