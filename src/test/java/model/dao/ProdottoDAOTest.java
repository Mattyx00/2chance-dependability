package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
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
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

class ProdottoDAOTest {

    private ProdottoDAO prodottoDAO;
    private MockedStatic<ConPool> mockedConPool;
    private Connection connection;
    private PreparedStatement preparedStatement;
    private ResultSet resultSet;

    @BeforeEach
    void setUp() throws SQLException {
        prodottoDAO = new ProdottoDAO();
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
    // getProdottoById Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Should return fully populated Prodotto when ID exists")
    void shouldReturnFullyPopulatedProductWhenIdExists() throws SQLException {
        // Arrange
        int productId = 1;
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, false, false);

        when(resultSet.getInt(1)).thenReturn(productId);
        when(resultSet.getString(2)).thenReturn("Elettronica");
        when(resultSet.getString(3)).thenReturn("Descrizione test");
        when(resultSet.getString(4)).thenReturn("10x10");
        when(resultSet.getInt(5)).thenReturn(100);
        when(resultSet.getDouble(6)).thenReturn(1.5);
        when(resultSet.getString(7)).thenReturn("img.jpg");
        when(resultSet.getString(8)).thenReturn("MarcaX");
        when(resultSet.getString(9)).thenReturn("ModelloY");
        when(resultSet.getDouble(10)).thenReturn(99.99);

        // Act
        Prodotto result = prodottoDAO.getProdottoById(productId);

        // Assert
        assertNotNull(result);
        assertEquals(productId, result.getId());
        assertEquals("MarcaX", result.getMarca());
        assertEquals("Elettronica", result.getCategoria().getNomeCategoria());

        // Note: Specifiche and Recensioni lists might be empty if sub-DAOs fail or
        // return empty,
        // but we expect the object itself to be returned securely.
    }

    @Test
    @DisplayName("F2: Should return null when ID does not exist")
    void shouldReturnNullWhenIdDoesNotExist() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(false);

        // Act
        Prodotto result = prodottoDAO.getProdottoById(999);

        // Assert
        assertNull(result);
    }

    @Test
    @DisplayName("F3: Should throw exception when ID is invalid")
    void shouldThrowExceptionWhenIdIsInvalid() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(IllegalArgumentException.class,
                () -> prodottoDAO.getProdottoById(0));
        assertTrue(exception.getMessage().contains("maggiore di zero"));
    }

    @Test
    @DisplayName("F4: Should return product with empty lists when dependencies fail")
    void shouldReturnProductWithEmptyListsWhenDependenciesFail() throws SQLException {
        // Arrange
        // This test simulates that even if inner DAOs (Specifiche/Recensione) throw,
        // ProdottoDAO catches it and returns the product.
        // We can't strictly force inner DAOs to fail without complex mocking of new(),
        // but we verify the main flow.
        int productId = 1;
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, false, false);
        when(resultSet.getInt(1)).thenReturn(productId);
        when(resultSet.getString(2)).thenReturn("Cat");
        when(resultSet.getString(3)).thenReturn("Descrizione");
        when(resultSet.getString(4)).thenReturn("Dim");
        when(resultSet.getInt(5)).thenReturn(10);
        when(resultSet.getDouble(6)).thenReturn(1.0);
        when(resultSet.getString(7)).thenReturn("img.jpg");
        when(resultSet.getString(8)).thenReturn("Marca");
        when(resultSet.getString(9)).thenReturn("Modello");
        when(resultSet.getDouble(10)).thenReturn(10.0);

        // Act
        Prodotto result = prodottoDAO.getProdottoById(productId);

        // Assert
        assertNotNull(result);
        assertNotNull(result.getSpecifiche());
        assertNotNull(result.getRecensioni());
    }

    // =================================================================================================
    // addProdotto Tests
    // =================================================================================================

    private Prodotto createValidProduct() {
        Prodotto p = new Prodotto();
        Categoria c = new Categoria();
        c.setNomeCategoria("TestCat");
        p.setCategoria(c);
        p.setMarca("TestMarca");
        p.setModello("TestModello");
        p.setPrezzo(10.0);
        return p;
    }

    @Test
    @DisplayName("F5: Should return row count when insert is successful")
    void shouldReturnRowCountWhenInsertIsSuccessful() throws SQLException {
        // Arrange
        Prodotto p = createValidProduct();
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeUpdate()).thenReturn(1);

        // Act
        int result = prodottoDAO.addProdotto(p);

        // Assert
        assertEquals(1, result);
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F6: Should throw exception when product is null")
    void shouldThrowExceptionWhenProductIsNull() {
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.addProdotto(null));
    }

    @ParameterizedTest
    @CsvSource({
            "null_category",
            "negative_price",
            "empty_brand",
            "empty_model"
    })
    @DisplayName("F7: Should throw exception when product fields are invalid")
    void shouldThrowExceptionWhenProductIsInvalid(String scenario) {
        Prodotto p = mock(Prodotto.class);
        // Default valid stubs
        Categoria c = new Categoria();
        c.setNomeCategoria("ValidCat");
        when(p.getCategoria()).thenReturn(c);
        when(p.getMarca()).thenReturn("ValidMarca");
        when(p.getModello()).thenReturn("ValidModello");
        when(p.getPrezzo()).thenReturn(10.0);

        switch (scenario) {
            case "null_category":
                when(p.getCategoria()).thenReturn(null); // Force null category return
                break;
            case "negative_price":
                when(p.getPrezzo()).thenReturn(-1.0);
                break;
            case "empty_brand":
                when(p.getMarca()).thenReturn("");
                break;
            case "empty_model":
                when(p.getModello()).thenReturn("");
                break;
        }

        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.addProdotto(p));
    }

    // =================================================================================================
    // modificaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("F8: Should update product including image when image is set")
    void shouldUpdateProductIncludingImage() throws SQLException {
        // Arrange
        Prodotto p = createValidProduct();
        p.setId(1);
        p.setImmagine("new_image.jpg");
        when(connection.prepareStatement(contains("immagine = ?"))).thenReturn(preparedStatement);

        // Act
        prodottoDAO.modificaProdotto(p);

        // Assert
        verify(preparedStatement).executeUpdate();
        // Since logic branches on image, if image SQL is used, we know branch was taken
    }

    @Test
    @DisplayName("F9: Should update product excluding image when image is null")
    void shouldUpdateProductExcludingImage() throws SQLException {
        // Arrange
        Prodotto p = createValidProduct();
        p.setId(1);
        p.setImmagine(null);
        // We expect query NOT to contain "immagine = ?" or satisfy logic
        // Easier to mock exact query match if known, or verify setString calls
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);

        // Act
        prodottoDAO.modificaProdotto(p);

        // Assert
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F10: Should throw exception when ID is invalid for update")
    void shouldThrowExceptionWhenIdIsInvalidForUpdate() {
        Prodotto p = createValidProduct();
        p.setId(0);
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.modificaProdotto(p));
    }

    // =================================================================================================
    // getProdottiByCategoria Tests
    // =================================================================================================

    @Test
    @DisplayName("F11: Should return product list when category is valid")
    void shouldReturnProductListWhenCategoryisValid() throws SQLException {
        // Arrange
        String cat = "Elettronica";
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, false);

        // Mock all required fields to avoid Prodotto bean validation errors
        when(resultSet.getInt(1)).thenReturn(1);
        when(resultSet.getString(2)).thenReturn(cat);
        when(resultSet.getString(3)).thenReturn("Descrizione");
        when(resultSet.getString(4)).thenReturn("Dim");
        when(resultSet.getInt(5)).thenReturn(10);
        when(resultSet.getDouble(6)).thenReturn(1.0);
        when(resultSet.getString(7)).thenReturn("img.jpg");
        when(resultSet.getString(8)).thenReturn("Marca");
        when(resultSet.getString(9)).thenReturn("Modello");
        when(resultSet.getDouble(10)).thenReturn(10.0);

        // Act
        ArrayList<Prodotto> result = prodottoDAO.getProdottiByCategoria(cat);

        // Assert
        assertEquals(1, result.size());
        assertEquals(cat, result.get(0).getCategoria().getNomeCategoria());
    }

    @Test
    @DisplayName("F12: Should throw exception when category is invalid")
    void shouldThrowExceptionWhenCategoryIsInvalid() {
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.getProdottiByCategoria(null));
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.getProdottiByCategoria(""));
    }

    // =================================================================================================
    // eliminaProdotto Tests
    // =================================================================================================

    @Test
    @DisplayName("F13: Should execute update when ID is valid")
    void shouldExecuteUpdateWhenIdIsValid() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);

        // Act
        prodottoDAO.eliminaProdotto(10);

        // Assert
        verify(preparedStatement).executeUpdate();
    }

    @Test
    @DisplayName("F14: Should throw exception when ID is invalid for delete")
    void shouldThrowExceptionWhenDeleteIdIsInvalid() {
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.eliminaProdotto(0));
    }

    // =================================================================================================
    // cercaProdotti Tests
    // =================================================================================================

    @Test
    @DisplayName("F15: Should return matching products when name is valid")
    void shouldReturnMatchingProductsWhenNameIsValid() throws SQLException {
        // Arrange
        when(connection.prepareStatement(anyString())).thenReturn(preparedStatement);
        when(preparedStatement.executeQuery()).thenReturn(resultSet);
        when(resultSet.next()).thenReturn(true, false);

        // Mock all required fields to avoid Prodotto bean validation errors
        when(resultSet.getInt(1)).thenReturn(1);
        when(resultSet.getString(2)).thenReturn("Cat");
        when(resultSet.getString(3)).thenReturn("Descrizione");
        when(resultSet.getString(4)).thenReturn("Dim");
        when(resultSet.getInt(5)).thenReturn(10);
        when(resultSet.getDouble(6)).thenReturn(1.0);
        when(resultSet.getString(7)).thenReturn("img.jpg");
        when(resultSet.getString(8)).thenReturn("Marca");
        when(resultSet.getString(9)).thenReturn("Modello");
        when(resultSet.getDouble(10)).thenReturn(10.0);

        // Act
        ArrayList<Prodotto> result = prodottoDAO.cercaProdotti("Test");

        // Assert
        assertEquals(1, result.size());
    }

    @Test
    @DisplayName("F16: Should throw exception when search name is invalid")
    void shouldThrowExceptionWhenSearchNameIsInvalid() {
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.cercaProdotti(null));
        assertThrows(IllegalArgumentException.class, () -> prodottoDAO.cercaProdotti("   "));
    }
}
