package model.beans;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ProdottoCarrelloTest {

    private Prodotto defaultProdotto;

    @BeforeEach
    void setUp() {
        defaultProdotto = createValidProduct(10.0);
    }

    private Prodotto createValidProduct(double price) {
        Prodotto product = new Prodotto();
        product.setPrezzo(price);
        return product;
    }

    // --- Constructor Tests ---

    // F01: Product is Null, Quantity is Valid -> IllegalArgumentException
    @Test
    @DisplayName("Constructor: Should throw IllegalArgumentException when product is null")
    void shouldThrowExceptionWhenProductIsNull_Constructor() {
        // Arrange
        Prodotto product = null;
        int quantity = 1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottoCarrello(product, quantity));
        assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    // F02: Product is Valid, Quantity is Negative -> IllegalArgumentException
    @Test
    @DisplayName("Constructor: Should throw IllegalArgumentException when quantity is negative")
    void shouldThrowExceptionWhenQuantityIsNegative_Constructor() {
        // Arrange
        Prodotto product = defaultProdotto;
        int quantity = -1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new ProdottoCarrello(product, quantity));
        assertEquals("La quantità non può essere negativa", exception.getMessage());
    }

    // F03: Product is Valid, Quantity is Zero -> Success
    @Test
    @DisplayName("Constructor: Should create object successfully when quantity is zero")
    void shouldCreateObjectWhenQuantityIsZero() {
        // Arrange
        Prodotto product = defaultProdotto;
        int quantity = 0;

        // Act
        ProdottoCarrello productCart = new ProdottoCarrello(product, quantity);

        // Assert
        assertAll("Verify object creation with zero quantity",
                () -> assertNotNull(productCart),
                () -> assertEquals(product, productCart.getProdotto()),
                () -> assertEquals(0, productCart.getQuantita()));
    }

    // F04: Product is Valid, Quantity is Positive -> Success
    @Test
    @DisplayName("Constructor: Should create object successfully when quantity is positive")
    void shouldCreateObjectWhenQuantityIsPositive() {
        // Arrange
        Prodotto product = defaultProdotto;
        int quantity = 5;

        // Act
        ProdottoCarrello productCart = new ProdottoCarrello(product, quantity);

        // Assert
        assertAll("Verify object creation with positive quantity",
                () -> assertNotNull(productCart),
                () -> assertEquals(product, productCart.getProdotto()),
                () -> assertEquals(5, productCart.getQuantita()));
    }

    // --- setProduct Tests ---

    // F05: Product is Null -> IllegalArgumentException
    @Test
    @DisplayName("setProduct: Should throw IllegalArgumentException when setting null product")
    void shouldThrowExceptionWhenSettingNullProduct() {
        // Arrange
        ProdottoCarrello productCart = new ProdottoCarrello(); // Default constructor

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> productCart.setProdotto(null));
        assertEquals("Il prodotto non può essere null", exception.getMessage());
    }

    // F06: Product is Valid -> Success
    @Test
    @DisplayName("setProduct: Should update product when valid")
    void shouldUpdateProductWhenValid() {
        // Arrange
        ProdottoCarrello productCart = new ProdottoCarrello();
        Prodotto newProduct = createValidProduct(20.0);

        // Act
        productCart.setProdotto(newProduct);

        // Assert
        assertEquals(newProduct, productCart.getProdotto());
    }

    // --- setQuantita Tests ---

    // F07: Quantity is Negative -> IllegalArgumentException
    @Test
    @DisplayName("setQuantita: Should throw IllegalArgumentException when setting negative quantity")
    void shouldThrowExceptionWhenSettingNegativeQuantity() {
        // Arrange
        ProdottoCarrello productCart = new ProdottoCarrello();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> productCart.setQuantita(-5));
        assertEquals("La quantità non può essere negativa", exception.getMessage());
    }

    // F08, F09: Quantity is Valid (Zero or Positive) -> Success
    @ParameterizedTest
    @CsvSource({
            "0", // F08
            "1", // F09
            "100" // F09
    })
    @DisplayName("setQuantita: Should update quantity when valid values provided")
    void shouldUpdateQuantitaWhenValidValuesProvided(int quantity) {
        // Arrange
        ProdottoCarrello productCart = new ProdottoCarrello();

        // Act
        productCart.setQuantita(quantity);

        // Assert
        assertEquals(quantity, productCart.getQuantita());
    }

    // --- getPrezzoTotale Tests ---

    // F10: Product is Null -> IllegalStateException
    @Test
    @DisplayName("getPrezzoTotale: Should throw IllegalStateException when product is not set")
    void shouldThrowIllegalStateWhenProductNotSet_GetPrezzoTotale() {
        // Arrange
        ProdottoCarrello productCart = new ProdottoCarrello(); // Product is null by default

        // Act & Assert
        IllegalStateException exception = assertThrows(
                IllegalStateException.class,
                () -> productCart.getPrezzoTotale());
        assertEquals("Impossibile calcolare il prezzo totale: prodotto non impostato", exception.getMessage());
    }

    // F11-F13: Valid combinations of Price and Quantity -> Return correct total
    @ParameterizedTest(name = "Price: {0}, Quantity: {1} -> Expected: {2}")
    @CsvSource({
            "10.0, 2, 20.0", // F13: Positive price, Positive quantity
            "5.5, 0, 0.0", // F11: Positive price, Zero quantity
            "0.0, 5, 0.0", // F12: Zero price, Positive quantity
            "15.5, 3, 46.5" // F13 additional case
    })
    @DisplayName("getPrezzoTotale: Should calculate correct total")
    void shouldCalculateCorrectTotal(double price, int quantity, double expectedTotal) {
        // Arrange
        Prodotto product = createValidProduct(price);
        ProdottoCarrello productCart = new ProdottoCarrello(product, quantity);

        // Act
        double totalProductCartPrice = productCart.getPrezzoTotale();

        // Assert
        assertEquals(expectedTotal, totalProductCartPrice, 0.001, "Total price calculation is incorrect");
    }
}
