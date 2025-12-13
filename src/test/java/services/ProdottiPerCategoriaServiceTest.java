package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.lang.reflect.Field;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class ProdottiPerCategoriaServiceTest {

    @Mock
    private ProdottoDAO prodottoDAO;

    @InjectMocks
    private ProdottiPerCategoriaService prodottiPerCategoriaService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("C2: Should instantiate service when DAO is non-null")
    void shouldInstantiateServiceWhenDAOIsNonNull() {
        // Act & Assert
        assertNotNull(prodottiPerCategoriaService);
    }

    @Test
    @DisplayName("C1: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottiPerCategoriaService(null));
        assertTrue(exception.getMessage().contains("ProdottoDAO cannot be null"));
    }

    // =================================================================================================
    // getProdottiByCategoria Tests
    // =================================================================================================

    @ParameterizedTest(name = "G1, G2, G3: Should throw exception when category is \"{0}\"")
    @NullAndEmptySource
    @DisplayName("G1, G2, G3: Should throw exception when category is invalid")
    void shouldThrowExceptionWhenCategoryIsInvalid(String invalidCategory) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> prodottiPerCategoriaService.getProdottiByCategoria(invalidCategory));
        assertTrue(exception.getMessage().contains("Category name cannot be null or empty"));
    }

    @Test
    @DisplayName("G5: Should return product list when category is valid and DAO returns list")
    void shouldReturnProductListWhenCategoryIsValid() throws SQLException {
        // Arrange
        String category = "Elettronica";

        ArrayList<Prodotto> expectedArrayProducts = new ArrayList<>();
        expectedArrayProducts.add(new Prodotto());

        when(prodottoDAO.getProdottiByCategoria(category)).thenReturn(expectedArrayProducts);

        // Act
        ArrayList<Prodotto> actualArrayProducts = prodottiPerCategoriaService.getProdottiByCategoria(category);

        // Assert
        assertAll(
                () -> assertNotNull(actualArrayProducts),
                () -> assertEquals(expectedArrayProducts, actualArrayProducts));

        verify(prodottoDAO).getProdottiByCategoria(category);
    }

    @Test
    @DisplayName("G6: Should return null when category is valid but DAO returns null")
    void shouldReturnNullWhenDAOReturnsNull() throws SQLException {
        // Arrange
        String category = "Elettronica";

        when(prodottoDAO.getProdottiByCategoria(category)).thenReturn(null);

        // Act
        ArrayList<Prodotto> arrayProducts = prodottiPerCategoriaService.getProdottiByCategoria(category);

        // Assert
        assertNull(arrayProducts);

        verify(prodottoDAO).getProdottiByCategoria(category);
    }

    @Test
    @DisplayName("G7: Should throw SQLException when DAO throws SQLException")
    void shouldThrowSQLExceptionWhenDAOThrows() throws SQLException {
        // Arrange
        String category = "Elettronica";

        when(prodottoDAO.getProdottiByCategoria(category)).thenThrow(new SQLException("DB Error"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> prodottiPerCategoriaService.getProdottiByCategoria(category));
        assertEquals("DB Error", exception.getMessage());

        verify(prodottoDAO).getProdottiByCategoria(category);
    }
}
