package services;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.ProdottoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class InitServiceTest {

    @Mock
    private CategoriaDAO categoriaDAO;

    @Mock
    private ProdottoDAO prodottoDAO;

    private InitService initService;

    @BeforeEach
    void setUp() {
        initService = new InitService(categoriaDAO, prodottoDAO);
    }

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF3: Should throw exception when CategoriaDAO is null")
    void shouldThrowExceptionWhenCategoriaDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new InitService(null, prodottoDAO));
        assertTrue(exception.getMessage().contains("CategoriaDAO cannot be null"));
    }

    @Test
    @DisplayName("TF4: Should throw exception when ProdottoDAO is null")
    void shouldThrowExceptionWhenProdottoDAOIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new InitService(categoriaDAO, null));
        assertTrue(exception.getMessage().contains("ProdottoDAO cannot be null"));
    }

    @Test
    @DisplayName("TF5: Should instantiate service when all DAOs are non-null")
    void shouldInitializeWhenBothDAOsAreValid() {
        // Act
        InitService service = new InitService(categoriaDAO, prodottoDAO);

        // Assert
        assertNotNull(service);
    }

    // =================================================================================================
    // getCategorie Tests
    // =================================================================================================

    @Test
    @DisplayName("TF6: Should return empty list when DAO returns null")
    void shouldReturnEmptyListWhenDaoReturnsNull() throws SQLException {
        // Arrange
        when(categoriaDAO.getCategorie()).thenReturn(null);

        // Act
        ArrayList<Categoria> arrayCategories = initService.getCategorie();

        // Assert
        assertAll(
                () -> assertNotNull(arrayCategories),
                () -> assertTrue(arrayCategories.isEmpty()));
    }

    @Test
    @DisplayName("TF7: Should return empty list when DAO returns empty list")
    void shouldReturnEmptyListWhenDaoReturnsEmptyList() throws SQLException {
        // Arrange
        when(categoriaDAO.getCategorie()).thenReturn(new ArrayList<>());

        // Act
        ArrayList<Categoria> arrayCategories = initService.getCategorie();

        // Assert
        assertAll(
                () -> assertNotNull(arrayCategories),
                () -> assertTrue(arrayCategories.isEmpty()));
    }

    @Test
    @DisplayName("TF8: Should return populated list when DAO returns populated list")
    void shouldReturnPopulatedListWhenDaoReturnsPopulatedList() throws SQLException {
        // Arrange
        ArrayList<Categoria> arrayCategories1 = new ArrayList<>();
        arrayCategories1.add(new Categoria());
        arrayCategories1.add(new Categoria());

        when(categoriaDAO.getCategorie()).thenReturn(arrayCategories1);

        // Act
        ArrayList<Categoria> arrayCategories2 = initService.getCategorie();

        // Assert
        assertAll(
                () -> assertEquals(2, arrayCategories2.size()),
                () -> assertEquals(arrayCategories1, arrayCategories2));
    }

    // =================================================================================================
    // getUltimiProdotti Tests
    // =================================================================================================

    @Test
    @DisplayName("TF10: Should return empty list when DAO returns null (Prodotto)")
    void shouldReturnEmptyListWhenProdottoDaoReturnsNull() throws SQLException {
        // Arrange
        when(prodottoDAO.getUltimiProdotti()).thenReturn(null);

        // Act
        ArrayList<Prodotto> arrayProducts = initService.getUltimiProdotti();

        // Assert
        assertAll(
                () -> assertNotNull(arrayProducts),
                () -> assertTrue(arrayProducts.isEmpty()));
    }

    @Test
    @DisplayName("TF11: Should return empty list when DAO returns empty list (Prodotto)")
    void shouldReturnEmptyListWhenProdottoDaoReturnsEmptyList() throws SQLException {
        // Arrange
        when(prodottoDAO.getUltimiProdotti()).thenReturn(new ArrayList<>());

        // Act
        ArrayList<Prodotto> arrayProducts = initService.getUltimiProdotti();

        // Assert
        assertAll(
                () -> assertNotNull(arrayProducts),
                () -> assertTrue(arrayProducts.isEmpty()));
    }

    @Test
    @DisplayName("TF12: Should return populated list when DAO returns populated list (Prodotto)")
    void shouldReturnPopulatedListWhenProdottoDaoReturnsPopulatedList() throws SQLException {
        // Arrange
        ArrayList<Prodotto> arrayProducts1 = new ArrayList<>();
        arrayProducts1.add(new Prodotto());
        arrayProducts1.add(new Prodotto());
        arrayProducts1.add(new Prodotto());
        arrayProducts1.add(new Prodotto());
        arrayProducts1.add(new Prodotto());

        when(prodottoDAO.getUltimiProdotti()).thenReturn(arrayProducts1);

        // Act
        ArrayList<Prodotto> arrayProducts2 = initService.getUltimiProdotti();

        // Assert
        assertAll(
                () -> assertEquals(5, arrayProducts2.size()),
                () -> assertEquals(arrayProducts1, arrayProducts2));
    }
}
